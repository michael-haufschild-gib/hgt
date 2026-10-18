import GaloisForLFunctions.TransHorizonIncidenceMechanics.QuotientSpectralGapAndOddChainCoercivity
import GaloisForLFunctions.TransHorizonIncidenceMechanics.CompactWindowedOfflineChainIntegralAndOriginCollarDuality
import GaloisForLFunctions.TransHorizonIncidenceMechanics.OddEigenvectorNodalModulusBalanceAndFourthBandStepLaw
import GaloisForLFunctions.RHTower.CHMDOddProfileArchAbsorptionAndPrimeChainBridge

/-!
# Odd–Even Bipartite Prime-Chain Parallelogram Law, Smooth Even Complex-Hyperbolic Collar Excess, and Off-Diagonal Stationary Positivity (`OddPolarCollarParallelogramAndPrimeClockBridge`)

This module advances **Step 2** (Origin-Crossing Collar Duality & Smooth Odd Polar Profiles) and
**Step 3 (Sub-routes 3A & 3B: Nodal & Finite-Packet Off-Diagonal Stationary Positivity)** of the
CHMD closure programme (`docs/reports/TransHorizonIncidenceMechanics/CHMD-programme.md`).

## Classical Baseline & New Mathematical Content

1. **Exact Odd–Even Bipartite Prime-Chain Parallelogram & Domination Laws (§1):**
   - *Classical baseline:* For an odd profile $v(-x) = -v(x)$, shifting across the origin flips
     sign ($v(u - \log k) = -v(\log k - u)$ when $u \le \log k$).
   - *New formulation & theorem:* On every bipartite prime-chain cut
     `(chainLeft N p b u, chainRight N p b u)`, every left node $m \in \operatorname{chainLeft}$
     satisfies $u - \log m > 0$ and every right node $k \in \operatorname{chainRight}$ satisfies
     $u - \log k \le 0$. Consequently, defining the even half-line fold
     $\operatorname{evenFold}(v, x) := v(|x|)$, **every** edge $(m, k) \in L \times R$ is an
     origin-straddling pair satisfying:
     $$v(u - \log m) - v(u - \log k) = \operatorname{evenFold}(v, u - \log m) + \operatorname{evenFold}(v, u - \log k).$$
     This yields the exact bipartite parallelogram and difference identities:
     $$\operatorname{bipartiteEnergy}(L, R, v(u - \log \cdot)) + \operatorname{bipartiteEnergy}(L, R, \operatorname{evenFold} v(u - \log \cdot))
       = 2 \sum_{m \in L} \sum_{k \in R} \bigl(v(u - \log m)^2 + v(u - \log k)^2\bigr),$$
     $$\operatorname{bipartiteEnergy}(L, R, v(u - \log \cdot)) - \operatorname{bipartiteEnergy}(L, R, \operatorname{evenFold} v(u - \log \cdot))
       = 4 \sum_{m \in L} \sum_{k \in R} \operatorname{evenFold}(v, u - \log m)\,\operatorname{evenFold}(v, u - \log k).$$
     In particular, whenever $v(x) \ge 0$ on $[0, \infty)$ (for instance, `oddPolarWeight a w` with
     $a > 0$ and $w \ge 0$), the origin flip **reinforces** every bipartite prime-chain jump:
     $$\operatorname{chainDensity}(N, p, b, \operatorname{evenFold} v, u) \le \operatorname{chainDensity}(N, p, b, v, u),$$
     $$\operatorname{density}(N, \operatorname{evenFold} v, u) \le \operatorname{density}(N, v, u),$$
     $$\operatorname{chainIntegral}(\operatorname{evenFold} v, q) \le \operatorname{chainIntegral}(v, q).$$
     (Classification: **Candidate new theorem**.)

2. **Smooth Even Complex-Hyperbolic Off-Line Pair & Exact $\gamma$-Free Collar Mixed Excess (§2):**
   - *Classical baseline:* The real and imaginary parts of $\cosh((\beta + i\gamma)x)$ are
     $\cosh(\beta x)\cos(\gamma x)$ and $\sinh(\beta x)\sin(\gamma x)$.
   - *New formulation & theorem:* Because $\sinh(\beta x)$ and $\sin(\gamma x)$ are both odd, their
     product $\sinh(\beta x)\sin(\gamma x)$ is **smooth ($C^\infty$) and even**, just like
     $\cosh(\beta x)\cos(\gamma x)$. Multiplying by any even smooth compactly supported window
     $w_0$ and the odd polar ground factor $\Psi_a(x)$ (`oddPolarWeight a`) produces two smooth
     compactly supported **odd** profiles in the exact domain of
     `oddProfileTest_markovEnergy_eq_chain_variances_sub_cosh` and
     `riemannHypothesis_iff_odd_primeChain_poincare`. Furthermore, the vertical oscillation
     $\gamma$ cancels identically in the two-channel square sum over the critical line ($\beta = 0$):
     $$\bigl(w_{\beta,\gamma}^{\mathrm{Re}}(x)\bigr)^2 + \bigl(w_{\beta,\gamma}^{\mathrm{Im}}(x)\bigr)^2
       - \bigl(w_{0,\gamma}^{\mathrm{Re}}(x)\bigr)^2 - \bigl(w_{0,\gamma}^{\mathrm{Im}}(x)\bigr)^2
       = \bigl(w_0(x)\sinh(\beta x)\bigr)^2,$$
     so the two-channel `oddProfileCollarMixed` density and per-divisor crossing + collar sum
     exceed their critical-line ($\beta = 0$) baselines by the exact positive $\sinh(\beta x)$
     collar mixed integral (`oddProfileCollarMixed_two_channel_sub_critical_eq`,
     `primeCrossing_add_oddProfileCollar_two_channel_sub_critical_eq`).
     (Classification: **Candidate new theorem**.)

3. **Finite-Packet Off-Diagonal Stationary Positivity Floor and Operator Decompositions (§3):**
   - *Classical baseline:* Finite-packet diagonal/off-diagonal splitting on Hilbert graphs.
   - *New formulation & theorem:* Because total stationary energy is a squared Hilbert norm
     (`0 ≤ stationaryEnergy (thetaProduct (∑ i ∈ S, a i).val.fst)`), the off-diagonal stationary
     sum of any finite packet $a : \iota \to \operatorname{SourceGraph}$ satisfies the universal
     lower bound
     $$\operatorname{offDiagStationarySum}(S, a)
       \ge -\sum_{i \in S} \operatorname{stationaryEnergy}(\operatorname{thetaProduct} a_i.\text{val.fst})
       \ge -(1 + \|\operatorname{groundPerturbation}\|) \sum_{i \in S} \|a_i\|^2,$$
     bounding `offDiagSourcePairSum S a` from below in terms of the off-diagonal archimedean and
     prime-shift operator sums (`offDiagSourcePairSum_ge_neg_diag_sub_arch_sub_primeShift`).
     (Classification: **New formulation / Corollary**.)
-/

open Finset MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDDoobGraph RHTower.CHMDClosedJump RHTower.CHMDPolar
open RHTower.CHMDPrimeChain RHTower.CHMDPrimeChainSource RHTower.CHMDPrimeCuts
open RHTower.PhiDivisorEnergy
open scoped InnerProductSpace BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ## §1. Exact Odd–Even Bipartite Prime-Chain Parallelogram & Domination Laws (`evenFold`) -/

/-- The even half-line fold of a profile $v : \mathbb{R} \to \mathbb{R}$:
$$\operatorname{evenFold}(v, x) := v(|x|).$$
When $v$ is odd and non-negative on $[0, \infty)$, $\operatorname{evenFold} v$ coincides with $|v|$. -/
def evenFold (v : ℝ → ℝ) (x : ℝ) : ℝ :=
  v |x|

/-- `evenFold v` is unconditionally even (`evenFold v (-x) = evenFold v x`).
(Classification: Known.) -/
theorem evenFold_even (v : ℝ → ℝ) (x : ℝ) :
    evenFold v (-x) = evenFold v x := by
  unfold evenFold
  rw [abs_neg]

/-- `evenFold v` is continuous whenever `v` is continuous. -/
theorem continuous_evenFold {v : ℝ → ℝ} (hv : Continuous v) :
    Continuous (evenFold v) :=
  hv.comp continuous_abs

/-- Every odd function $v : \mathbb{R} \to \mathbb{R}$ vanishes at $0$. -/
theorem odd_apply_zero {v : ℝ → ℝ} (hodd : ∀ x, v (-x) = -v x) :
    v 0 = 0 := by
  have h := hodd 0
  rw [neg_zero] at h
  linarith

/-- For an odd function $v$, `evenFold v x = v x` for $x \ge 0$ and `evenFold v x = -v x` for $x \le 0$. -/
theorem evenFold_of_nonneg {v : ℝ → ℝ} {x : ℝ} (hx : 0 ≤ x) :
    evenFold v x = v x := by
  unfold evenFold
  rw [abs_of_nonneg hx]

theorem evenFold_of_nonpos_of_odd {v : ℝ → ℝ} (hodd : ∀ x, v (-x) = -v x) {x : ℝ} (hx : x ≤ 0) :
    evenFold v x = -v x := by
  unfold evenFold
  rw [abs_of_nonpos hx, hodd]

/-- For every odd function $v$, `evenFold v x ^ 2 = v x ^ 2` for all $x \in \mathbb{R}$. -/
theorem evenFold_sq_eq_of_odd {v : ℝ → ℝ} (hodd : ∀ x, v (-x) = -v x) (x : ℝ) :
    evenFold v x ^ (2 : ℕ) = v x ^ (2 : ℕ) := by
  rcases le_total 0 x with hx | hx
  · rw [evenFold_of_nonneg hx]
  · rw [evenFold_of_nonpos_of_odd hodd hx, neg_sq]

/-- **Origin-Straddling Jump Identity on Prime Chains (`odd_sub_eq_evenFold_add_of_mem_chain`):**
For every odd function $v : \mathbb{R} \to \mathbb{R}$, every $N, p, b : \mathbb{N}$, every cut
$u \in \mathbb{R}$, and every pair $(m, k) \in \operatorname{chainLeft}(N, p, b, u) \times \operatorname{chainRight}(N, p, b, u)$:
$$v(u - \log m) - v(u - \log k)
  = \operatorname{evenFold}(v, u - \log m) + \operatorname{evenFold}(v, u - \log k).$$
(Classification: Candidate new theorem.) -/
theorem odd_sub_eq_evenFold_add_of_mem_chain {v : ℝ → ℝ} (hodd : ∀ x, v (-x) = -v x)
    {N p b m k : ℕ} {u : ℝ}
    (hm : m ∈ chainLeft N p b u) (hk : k ∈ chainRight N p b u) :
    v (u - Real.log (m : ℝ)) - v (u - Real.log (k : ℝ)) =
      evenFold v (u - Real.log (m : ℝ)) + evenFold v (u - Real.log (k : ℝ)) := by
  unfold chainLeft at hm
  unfold chainRight at hk
  simp only [Finset.mem_filter] at hm hk
  have hm_nonneg : 0 ≤ u - Real.log (m : ℝ) := by linarith [hm.2.2]
  have hk_nonpos : u - Real.log (k : ℝ) ≤ 0 := by linarith [hk.2.2]
  rw [evenFold_of_nonneg hm_nonneg, evenFold_of_nonpos_of_odd hodd hk_nonpos]
  ring

/-- **Pointwise Odd–Even Bipartite Prime-Chain Parallelogram & Difference Identities
(`odd_chain_jump_sq_parallelogram_and_diff`):**
For every odd function $v : \mathbb{R} \to \mathbb{R}$ and every edge
$(m, k) \in \operatorname{chainLeft}(N, p, b, u) \times \operatorname{chainRight}(N, p, b, u)$:
1. $(v(u - \log m) - v(u - \log k))^2 + (\operatorname{evenFold} v (u - \log m) - \operatorname{evenFold} v (u - \log k))^2 = 2(v(u - \log m)^2 + v(u - \log k)^2)$,
2. $(v(u - \log m) - v(u - \log k))^2 - (\operatorname{evenFold} v (u - \log m) - \operatorname{evenFold} v (u - \log k))^2 = 4\,\operatorname{evenFold} v (u - \log m)\,\operatorname{evenFold} v (u - \log k)$.
(Classification: Candidate new theorem.) -/
theorem odd_chain_jump_sq_parallelogram_and_diff {v : ℝ → ℝ} (hodd : ∀ x, v (-x) = -v x)
    {N p b m k : ℕ} {u : ℝ}
    (hm : m ∈ chainLeft N p b u) (hk : k ∈ chainRight N p b u) :
    ((v (u - Real.log (m : ℝ)) - v (u - Real.log (k : ℝ))) ^ (2 : ℕ) +
        (evenFold v (u - Real.log (m : ℝ)) - evenFold v (u - Real.log (k : ℝ))) ^ (2 : ℕ) =
      2 * (v (u - Real.log (m : ℝ)) ^ (2 : ℕ) + v (u - Real.log (k : ℝ)) ^ (2 : ℕ))) ∧
    ((v (u - Real.log (m : ℝ)) - v (u - Real.log (k : ℝ))) ^ (2 : ℕ) -
        (evenFold v (u - Real.log (m : ℝ)) - evenFold v (u - Real.log (k : ℝ))) ^ (2 : ℕ) =
      4 * evenFold v (u - Real.log (m : ℝ)) * evenFold v (u - Real.log (k : ℝ))) := by
  have hsub := odd_sub_eq_evenFold_add_of_mem_chain hodd hm hk
  have hsqm := evenFold_sq_eq_of_odd hodd (u - Real.log (m : ℝ))
  have hsqk := evenFold_sq_eq_of_odd hodd (u - Real.log (k : ℝ))
  rw [hsub]
  constructor
  · linear_combination 2 * hsqm + 2 * hsqk
  · ring

/-- **Bipartite Prime-Chain Difference Identity for Odd Profiles (`bipartiteEnergy_odd_sub_evenFold_eq`):**
For every odd function $v : \mathbb{R} \to \mathbb{R}$ and every $N, p, b : \mathbb{N}$, $u \in \mathbb{R}$:
$$\operatorname{bipartiteEnergy}(L, R, x \mapsto v(u - \log x))
  - \operatorname{bipartiteEnergy}(L, R, x \mapsto \operatorname{evenFold} v (u - \log x))
  = 4 \sum_{m \in L} \sum_{k \in R} \operatorname{evenFold} v (u - \log m)\,\operatorname{evenFold} v (u - \log k).$$
(Classification: Candidate new theorem.) -/
theorem bipartiteEnergy_odd_sub_evenFold_eq {v : ℝ → ℝ} (hodd : ∀ x, v (-x) = -v x)
    (N p b : ℕ) (u : ℝ) :
    bipartiteEnergy (chainLeft N p b u) (chainRight N p b u)
        (fun m => v (u - Real.log (m : ℝ))) -
      bipartiteEnergy (chainLeft N p b u) (chainRight N p b u)
        (fun m => evenFold v (u - Real.log (m : ℝ))) =
      4 * ∑ m ∈ chainLeft N p b u, ∑ k ∈ chainRight N p b u,
        evenFold v (u - Real.log (m : ℝ)) * evenFold v (u - Real.log (k : ℝ)) := by
  unfold bipartiteEnergy
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hd := (odd_chain_jump_sq_parallelogram_and_diff hodd hm hk).2
  linarith

/-- **Bipartite Prime-Chain Parallelogram Identity for Odd Profiles (`bipartiteEnergy_odd_add_evenFold_eq`):**
For every odd function $v : \mathbb{R} \to \mathbb{R}$ and every $N, p, b : \mathbb{N}$, $u \in \mathbb{R}$:
$$\operatorname{bipartiteEnergy}(L, R, x \mapsto v(u - \log x))
  + \operatorname{bipartiteEnergy}(L, R, x \mapsto \operatorname{evenFold} v (u - \log x))
  = 2 \sum_{m \in L} \sum_{k \in R} \bigl(v(u - \log m)^2 + v(u - \log k)^2\bigr).$$
(Classification: Candidate new theorem.) -/
theorem bipartiteEnergy_odd_add_evenFold_eq {v : ℝ → ℝ} (hodd : ∀ x, v (-x) = -v x)
    (N p b : ℕ) (u : ℝ) :
    bipartiteEnergy (chainLeft N p b u) (chainRight N p b u)
        (fun m => v (u - Real.log (m : ℝ))) +
      bipartiteEnergy (chainLeft N p b u) (chainRight N p b u)
        (fun m => evenFold v (u - Real.log (m : ℝ))) =
      2 * ∑ m ∈ chainLeft N p b u, ∑ k ∈ chainRight N p b u,
        (v (u - Real.log (m : ℝ)) ^ (2 : ℕ) + v (u - Real.log (k : ℝ)) ^ (2 : ℕ)) := by
  unfold bipartiteEnergy
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  exact (odd_chain_jump_sq_parallelogram_and_diff hodd hm hk).1

/-- **Half-Line Positive Odd Domination on `varianceEnergy` (`varianceEnergy_odd_ge_evenFold_of_nonneg_Ici`):**
If $v : \mathbb{R} \to \mathbb{R}$ is odd (`∀ x, v (-x) = -v x`) and non-negative on $[0, \infty)$
(`∀ x ≥ 0, 0 ≤ v x`), then at every scale $N, p, b : \mathbb{N}$ and every cut $u \in \mathbb{R}$:
$$\operatorname{varianceEnergy}(L, R, x \mapsto \operatorname{evenFold} v (u - \log x))
  \le \operatorname{varianceEnergy}(L, R, x \mapsto v(u - \log x)).$$
(Classification: Candidate new theorem.) -/
theorem varianceEnergy_odd_ge_evenFold_of_nonneg_Ici {v : ℝ → ℝ}
    (hodd : ∀ x, v (-x) = -v x) (hnn : ∀ x : ℝ, 0 ≤ x → 0 ≤ v x)
    (N p b : ℕ) (u : ℝ) :
    varianceEnergy (chainLeft N p b u) (chainRight N p b u)
        (fun m => evenFold v (u - Real.log (m : ℝ))) ≤
      varianceEnergy (chainLeft N p b u) (chainRight N p b u)
        (fun m => v (u - Real.log (m : ℝ))) := by
  rw [← bipartiteEnergy_eq_variance, ← bipartiteEnergy_eq_variance]
  have hdiff := bipartiteEnergy_odd_sub_evenFold_eq hodd N p b u
  have hsum_nn : 0 ≤ 4 * ∑ m ∈ chainLeft N p b u, ∑ k ∈ chainRight N p b u,
      evenFold v (u - Real.log (m : ℝ)) * evenFold v (u - Real.log (k : ℝ)) := by
    refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun k _ => ?_)
    exact mul_nonneg (hnn _ (abs_nonneg _)) (hnn _ (abs_nonneg _))
  linarith

/-- **Half-Line Positive Odd Domination on `chainDensity` (`chainDensity_odd_ge_evenFold_of_nonneg_Ici`):**
If $v : \mathbb{R} \to \mathbb{R}$ is odd (`∀ x, v (-x) = -v x`) and non-negative on $[0, \infty)$
(`∀ x ≥ 0, 0 ≤ v x`), then for every positive product index $N : \mathbb{N}_+$, prime factor
$p \in N.\text{primeFactors}$, base $b \in \mathbb{N}$, and cut $u \in \mathbb{R}$:
$$\operatorname{chainDensity}(N, p, b, \operatorname{evenFold} v, u)
  \le \operatorname{chainDensity}(N, p, b, v, u).$$
(Classification: Candidate new theorem.) -/
theorem chainDensity_odd_ge_evenFold_of_nonneg_Ici {v : ℝ → ℝ}
    (hodd : ∀ x, v (-x) = -v x) (hnn : ∀ x : ℝ, 0 ≤ x → 0 ≤ v x)
    (N : ℕ+) {p : ℕ} (hp : p ∈ (N : ℕ).primeFactors) (b : ℕ) (u : ℝ) :
    chainDensity (N : ℕ) p b (evenFold v) u ≤ chainDensity (N : ℕ) p b v u := by
  by_cases hu : u ∈ Ioo (0 : ℝ) (Real.log (N : ℕ))
  · unfold chainDensity
    have hcoeff : 0 ≤ Real.log (p : ℝ) * fiber (N : ℕ) u :=
      mul_nonneg
        (Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le))
        (fiber_pos_on_central N.pos hu.1.le hu.2.le).le
    exact mul_le_mul_of_nonneg_left
      (varianceEnergy_odd_ge_evenFold_of_nonneg_Ici hodd hnn N p b u)
      hcoeff
  · simp only [chainDensity, chainVariance_term_zero_outside _ _ _ _ _ hu, mul_zero, le_rfl]

/-- **Half-Line Positive Odd Domination on Total Prime-Chain `density` (`density_odd_ge_evenFold_of_nonneg_Ici`):**
If $v : \mathbb{R} \to \mathbb{R}$ is odd and non-negative on $[0, \infty)$, then for all $N : \mathbb{N}_+$
and $u \in \mathbb{R}$:
$$\operatorname{density}(N, \operatorname{evenFold} v, u) \le \operatorname{density}(N, v, u).$$
(Classification: Corollary.) -/
theorem density_odd_ge_evenFold_of_nonneg_Ici {v : ℝ → ℝ}
    (hodd : ∀ x, v (-x) = -v x) (hnn : ∀ x : ℝ, 0 ≤ x → 0 ≤ v x)
    (N : ℕ+) (u : ℝ) :
    density (N : ℕ) (evenFold v) u ≤ density (N : ℕ) v u := by
  rw [density_eq_sum_chains, density_eq_sum_chains]
  refine Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun b _ => ?_
  exact chainDensity_odd_ge_evenFold_of_nonneg_Ici hodd hnn N hp b u

/-- For an odd function $v$, `evenFold v` has the exact same support and topological support as $v$,
and therefore inherits `HasCompactSupport`. -/
theorem hasCompactSupport_evenFold_of_odd {v : ℝ → ℝ} (hodd : ∀ x, v (-x) = -v x)
    (hvc : HasCompactSupport v) :
    HasCompactSupport (evenFold v) := by
  have hsupp : Function.support (evenFold v) = Function.support v := by
    ext x
    simp only [Function.mem_support, ne_eq]
    rcases le_total 0 x with hx | hx
    · rw [evenFold_of_nonneg hx]
    · rw [evenFold_of_nonpos_of_odd hodd hx, neg_eq_zero]
  unfold HasCompactSupport tsupport at hvc ⊢
  rwa [hsupp]

/-- **Half-Line Positive Odd Domination on Integrated `chainIntegral` (`chainIntegral_odd_ge_evenFold_of_nonneg_Ici`):**
For every continuous compactly supported odd profile $v : \mathbb{R} \to \mathbb{R}$ that is
non-negative on $[0, \infty)$, and every chain index $q : \operatorname{ChainIndex}$:
$$\operatorname{chainIntegral}(\operatorname{evenFold} v, q) \le \operatorname{chainIntegral}(v, q).$$
(Classification: Candidate new theorem.) -/
theorem chainIntegral_odd_ge_evenFold_of_nonneg_Ici {v : ℝ → ℝ}
    (hv : Continuous v) (hvc : HasCompactSupport v)
    (hodd : ∀ x, v (-x) = -v x) (hnn : ∀ x : ℝ, 0 ≤ x → 0 ≤ v x)
    (q : ChainIndex) :
    chainIntegral (evenFold v) q ≤ chainIntegral v q := by
  unfold chainIntegral
  have hev_cont : Continuous (evenFold v) := continuous_evenFold hv
  have hev_supp : HasCompactSupport (evenFold v) := hasCompactSupport_evenFold_of_odd hodd hvc
  have hint_ev := integrable_chainDensity q.1 q.2.1.property q.2.2.property hev_cont hev_supp
  have hint_v := integrable_chainDensity q.1 q.2.1.property q.2.2.property hv hvc
  exact integral_mono hint_ev hint_v fun u =>
    chainDensity_odd_ge_evenFold_of_nonneg_Ici hodd hnn q.1 q.2.1.property q.2.2.val u

/-- For $a > 0$ and any non-negative even profile $w \ge 0$, the secondary Doob gauge profile
`oddPolarWeight a w` is odd and non-negative on $[0, \infty)$, so its `chainDensity`, `density`,
and `chainIntegral` dominate those of `evenFold (oddPolarWeight a w)`.
(Classification: Corollary.) -/
theorem oddPolarWeight_nonneg_Ici {a : ℝ} (ha : 0 < a) {w : ℝ → ℝ}
    (hw_nn : ∀ x, 0 ≤ w x) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ oddPolarWeight a w x := by
  unfold oddPolarWeight
  rcases eq_or_lt_of_le hx with rfl | hpos
  · have h0 : oddPolarFunction a 0 = 0 := odd_apply_zero (oddPolarFunction_neg a)
    rw [h0, zero_mul]
  · exact mul_nonneg (oddPolarFunction_pos ha hpos).le (hw_nn x)

theorem chainIntegral_oddPolarWeight_ge_evenFold {a : ℝ} (ha : 0 < a) {w : ℝ → ℝ}
    (hw : Continuous w) (hwc : HasCompactSupport w)
    (heven : ∀ x, w (-x) = w x) (hw_nn : ∀ x, 0 ≤ w x) (q : ChainIndex) :
    chainIntegral (evenFold (oddPolarWeight a w)) q ≤
      chainIntegral (oddPolarWeight a w) q :=
  chainIntegral_odd_ge_evenFold_of_nonneg_Ici
    (continuous_oddPolarWeight a hw)
    (hasCompactSupport_oddPolarWeight a hwc)
    (oddPolarWeight_odd_of_even a heven)
    (fun _ hx => oddPolarWeight_nonneg_Ici ha hw_nn hx)
    q

/-! ## §2. Smooth Even Complex-Hyperbolic Off-Line Pair & Exact $\gamma$-Free Collar Mixed Excess -/

/-- The real-part smooth even off-line test wave:
$$w_{\beta,\gamma}^{\mathrm{Re}}(x) := w_0(x)\,\cosh(\beta x)\,\cos(\gamma x).$$ -/
def evenOfflineWaveCos (β γ : ℝ) (w₀ : ℝ → ℝ) (x : ℝ) : ℝ :=
  w₀ x * Real.cosh (β * x) * Real.cos (γ * x)

/-- The imaginary-part smooth even off-line test wave:
$$w_{\beta,\gamma}^{\mathrm{Im}}(x) := w_0(x)\,\sinh(\beta x)\,\sin(\gamma x).$$
Because $\sinh(\beta x)$ and $\sin(\gamma x)$ are both odd, their product is smooth and even! -/
def evenOfflineWaveSin (β γ : ℝ) (w₀ : ℝ → ℝ) (x : ℝ) : ℝ :=
  w₀ x * Real.sinh (β * x) * Real.sin (γ * x)

/-- The pure hyperbolic-sine radial envelope:
$$w_{\beta}^{\sinh}(x) := w_0(x)\,\sinh(\beta x).$$ -/
def evenOfflineSinhEnvelope (β : ℝ) (w₀ : ℝ → ℝ) (x : ℝ) : ℝ :=
  w₀ x * Real.sinh (β * x)

/-- Whenever $w_0$ is even (`∀ x, w₀ (-x) = w₀ x`), both `evenOfflineWaveCos β γ w₀` and
`evenOfflineWaveSin β γ w₀` are even functions of $x$.
(Classification: New formulation.) -/
theorem evenOfflineWaveCos_even (β γ : ℝ) {w₀ : ℝ → ℝ} (heven : ∀ x, w₀ (-x) = w₀ x) (x : ℝ) :
    evenOfflineWaveCos β γ w₀ (-x) = evenOfflineWaveCos β γ w₀ x := by
  unfold evenOfflineWaveCos
  rw [heven, mul_neg β x, Real.cosh_neg, mul_neg γ x, Real.cos_neg]

theorem evenOfflineWaveSin_even (β γ : ℝ) {w₀ : ℝ → ℝ} (heven : ∀ x, w₀ (-x) = w₀ x) (x : ℝ) :
    evenOfflineWaveSin β γ w₀ (-x) = evenOfflineWaveSin β γ w₀ x := by
  unfold evenOfflineWaveSin
  rw [heven, mul_neg β x, Real.sinh_neg, mul_neg γ x, Real.sin_neg]
  ring

theorem continuous_evenOfflineWaveCos (β γ : ℝ) {w₀ : ℝ → ℝ} (hw₀ : Continuous w₀) :
    Continuous (evenOfflineWaveCos β γ w₀) := by
  unfold evenOfflineWaveCos
  fun_prop

theorem continuous_evenOfflineWaveSin (β γ : ℝ) {w₀ : ℝ → ℝ} (hw₀ : Continuous w₀) :
    Continuous (evenOfflineWaveSin β γ w₀) := by
  unfold evenOfflineWaveSin
  fun_prop

theorem continuous_evenOfflineSinhEnvelope (β : ℝ) {w₀ : ℝ → ℝ} (hw₀ : Continuous w₀) :
    Continuous (evenOfflineSinhEnvelope β w₀) := by
  unfold evenOfflineSinhEnvelope
  fun_prop

theorem contDiff_evenOfflineWaveCos {n : ℕ∞} (β γ : ℝ) {w₀ : ℝ → ℝ} (hw₀ : ContDiff ℝ n w₀) :
    ContDiff ℝ n (evenOfflineWaveCos β γ w₀) := by
  unfold evenOfflineWaveCos
  exact (hw₀.mul (Real.contDiff_cosh.comp (contDiff_const.mul contDiff_id))).mul
    (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id))

theorem contDiff_evenOfflineWaveSin {n : ℕ∞} (β γ : ℝ) {w₀ : ℝ → ℝ} (hw₀ : ContDiff ℝ n w₀) :
    ContDiff ℝ n (evenOfflineWaveSin β γ w₀) := by
  unfold evenOfflineWaveSin
  exact (hw₀.mul (Real.contDiff_sinh.comp (contDiff_const.mul contDiff_id))).mul
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_id))

theorem hasCompactSupport_evenOfflineWaveCos (β γ : ℝ) {w₀ : ℝ → ℝ} (hwc : HasCompactSupport w₀) :
    HasCompactSupport (evenOfflineWaveCos β γ w₀) := by
  have heq : evenOfflineWaveCos β γ w₀ = fun x => w₀ x * (Real.cosh (β * x) * Real.cos (γ * x)) := by
    ext x; unfold evenOfflineWaveCos; ring
  rw [heq]
  exact hwc.mul_right

theorem hasCompactSupport_evenOfflineWaveSin (β γ : ℝ) {w₀ : ℝ → ℝ} (hwc : HasCompactSupport w₀) :
    HasCompactSupport (evenOfflineWaveSin β γ w₀) := by
  have heq : evenOfflineWaveSin β γ w₀ = fun x => w₀ x * (Real.sinh (β * x) * Real.sin (γ * x)) := by
    ext x; unfold evenOfflineWaveSin; ring
  rw [heq]
  exact hwc.mul_right

/-- **Exact Pointwise $\gamma$-Cancellation in the Smooth Even Complex-Hyperbolic Square Sum
(`evenOfflineWave_sq_sum_sub_critical_eq`):**
For all $\beta, \gamma, x \in \mathbb{R}$ and $w_0 : \mathbb{R} \to \mathbb{R}$, the vertical
frequency $\gamma$ cancels identically between the two smooth even channels over the critical line
($\beta = 0$):
$$\bigl(w_{\beta,\gamma}^{\mathrm{Re}}(x)\bigr)^2 + \bigl(w_{\beta,\gamma}^{\mathrm{Im}}(x)\bigr)^2
  - \bigl(w_{0,\gamma}^{\mathrm{Re}}(x)\bigr)^2 - \bigl(w_{0,\gamma}^{\mathrm{Im}}(x)\bigr)^2
  = \bigl(w_0(x)\sinh(\beta x)\bigr)^2.$$
(Classification: Candidate new theorem.) -/
theorem evenOfflineWave_sq_sum_sub_critical_eq (β γ : ℝ) (w₀ : ℝ → ℝ) (x : ℝ) :
    evenOfflineWaveCos β γ w₀ x ^ (2 : ℕ) + evenOfflineWaveSin β γ w₀ x ^ (2 : ℕ) -
        evenOfflineWaveCos 0 γ w₀ x ^ (2 : ℕ) - evenOfflineWaveSin 0 γ w₀ x ^ (2 : ℕ) =
      evenOfflineSinhEnvelope β w₀ x ^ (2 : ℕ) := by
  unfold evenOfflineWaveCos evenOfflineWaveSin evenOfflineSinhEnvelope
  rw [zero_mul, Real.cosh_zero, Real.sinh_zero]
  have htrig : Real.cos (γ * x) ^ (2 : ℕ) + Real.sin (γ * x) ^ (2 : ℕ) = 1 :=
    Real.cos_sq_add_sin_sq (γ * x)
  have hhyp : Real.cosh (β * x) ^ (2 : ℕ) - Real.sinh (β * x) ^ (2 : ℕ) = 1 :=
    Real.cosh_sq_sub_sinh_sq (β * x)
  linear_combination
    w₀ x ^ (2 : ℕ) * Real.cos (γ * x) ^ (2 : ℕ) * hhyp +
      w₀ x ^ (2 : ℕ) * Real.sinh (β * x) ^ (2 : ℕ) * htrig

/-- **Exact $\gamma$-Free Two-Channel `oddProfileCollarMixed` Off-Line Excess Identity
(`oddProfileCollarMixed_two_channel_sub_critical_eq`):**
For every $a, \beta, \gamma, t, x \in \mathbb{R}$ and $w_0 : \mathbb{R} \to \mathbb{R}$:
$$\operatorname{oddProfileCollarMixed}(a, w_{\beta,\gamma}^{\mathrm{Re}}, t, x)
  + \operatorname{oddProfileCollarMixed}(a, w_{\beta,\gamma}^{\mathrm{Im}}, t, x)
  - \operatorname{oddProfileCollarMixed}(a, w_{0,\gamma}^{\mathrm{Re}}, t, x)
  - \operatorname{oddProfileCollarMixed}(a, w_{0,\gamma}^{\mathrm{Im}}, t, x)
  = \operatorname{oddProfileCollarMixed}(a, w_{\beta}^{\sinh}, t, x).$$
When $a > 0$ and $x \in (0, t)$, this excess is unconditionally non-negative.
(Classification: Candidate new theorem.) -/
theorem oddProfileCollarMixed_two_channel_sub_critical_eq (a β γ : ℝ) (w₀ : ℝ → ℝ) (t x : ℝ) :
    oddProfileCollarMixed a (evenOfflineWaveCos β γ w₀) t x +
        oddProfileCollarMixed a (evenOfflineWaveSin β γ w₀) t x -
        oddProfileCollarMixed a (evenOfflineWaveCos 0 γ w₀) t x -
        oddProfileCollarMixed a (evenOfflineWaveSin 0 γ w₀) t x =
      oddProfileCollarMixed a (evenOfflineSinhEnvelope β w₀) t x := by
  have hx := evenOfflineWave_sq_sum_sub_critical_eq β γ w₀ x
  have htx := evenOfflineWave_sq_sum_sub_critical_eq β γ w₀ (t - x)
  unfold oddProfileCollarMixed
  linear_combination
    riemannKernelReal x * riemannKernelReal (t - x) *
      (oddPolarFunction a x + oddPolarFunction a (t - x)) *
      (oddPolarFunction a x * hx + oddPolarFunction a (t - x) * htx)

/-- Non-negativity of the two-channel `oddProfileCollarMixed` off-line excess on $x \in (0, t)$
for $a > 0$. -/
theorem oddProfileCollarMixed_two_channel_sub_critical_nonneg {a t x : ℝ} (ha : 0 < a)
    (hx : x ∈ Ioo (0 : ℝ) t) (β γ : ℝ) (w₀ : ℝ → ℝ) :
    0 ≤ oddProfileCollarMixed a (evenOfflineWaveCos β γ w₀) t x +
        oddProfileCollarMixed a (evenOfflineWaveSin β γ w₀) t x -
        oddProfileCollarMixed a (evenOfflineWaveCos 0 γ w₀) t x -
        oddProfileCollarMixed a (evenOfflineWaveSin 0 γ w₀) t x := by
  rw [oddProfileCollarMixed_two_channel_sub_critical_eq]
  exact oddProfileCollarMixed_nonneg ha hx (evenOfflineSinhEnvelope β w₀)

/-- The combined per-divisor `Θ`-Doob prime crossing and `m_a`-Doob prime collar integral for an
even profile $w$:
$$\mathcal{C}_{a,d}(w) := \operatorname{primeCrossing}(\operatorname{oddPolarWeight} a w, d)
  + \operatorname{vonMangoldtAtom} d \cdot \int_{x \in (0, \log d)} \operatorname{oddProfileCollarDiffSq}(a, w, \log d, x)\,dx.$$ -/
def primeCrossingWithOddCollar (a : ℝ) (w : ℝ → ℝ) (d : ℕ) : ℝ :=
  primeCrossing (oddPolarWeight a w) d +
    vonMangoldtAtom d * ∫ x in Ioo (0 : ℝ) (Real.log d),
      oddProfileCollarDiffSq a w (Real.log d) x

/-- **Per-Divisor Two-Channel Crossing + Collar Off-Line Excess Theorem
(`primeCrossingWithOddCollar_two_channel_sub_critical_eq`):**
For any continuous compactly supported even window $w_0 : \mathbb{R} \to \mathbb{R}$, any
$a, \beta, \gamma \in \mathbb{R}$, and any $d \in \mathbb{N}$:
$$\mathcal{C}_{a,d}(w_{\beta,\gamma}^{\mathrm{Re}}) + \mathcal{C}_{a,d}(w_{\beta,\gamma}^{\mathrm{Im}})
  - \mathcal{C}_{a,d}(w_{0,\gamma}^{\mathrm{Re}}) - \mathcal{C}_{a,d}(w_{0,\gamma}^{\mathrm{Im}})
  = \operatorname{vonMangoldtAtom} d \cdot \int_{x \in (0, \log d)}
      \operatorname{oddProfileCollarMixed}(a, w_{\beta}^{\sinh}, \log d, x)\,dx.$$
When $a > 0$, this per-divisor off-line excess is unconditionally non-negative.
(Classification: Candidate new theorem.) -/
theorem primeCrossingWithOddCollar_two_channel_sub_critical_eq (a β γ : ℝ) {w₀ : ℝ → ℝ}
    (hw₀ : Continuous w₀) (hwc : HasCompactSupport w₀) (heven : ∀ x, w₀ (-x) = w₀ x) (d : ℕ) :
    primeCrossingWithOddCollar a (evenOfflineWaveCos β γ w₀) d +
        primeCrossingWithOddCollar a (evenOfflineWaveSin β γ w₀) d -
        primeCrossingWithOddCollar a (evenOfflineWaveCos 0 γ w₀) d -
        primeCrossingWithOddCollar a (evenOfflineWaveSin 0 γ w₀) d =
      vonMangoldtAtom d * ∫ x in Ioo (0 : ℝ) (Real.log d),
        oddProfileCollarMixed a (evenOfflineSinhEnvelope β w₀) (Real.log d) x := by
  have h1 := primeCrossing_oddPolarWeight_add_oddProfileCollar_eq_mixed a
    (continuous_evenOfflineWaveCos β γ hw₀) (hasCompactSupport_evenOfflineWaveCos β γ hwc)
    (evenOfflineWaveCos_even β γ heven) d
  have h2 := primeCrossing_oddPolarWeight_add_oddProfileCollar_eq_mixed a
    (continuous_evenOfflineWaveSin β γ hw₀) (hasCompactSupport_evenOfflineWaveSin β γ hwc)
    (evenOfflineWaveSin_even β γ heven) d
  have h3 := primeCrossing_oddPolarWeight_add_oddProfileCollar_eq_mixed a
    (continuous_evenOfflineWaveCos 0 γ hw₀) (hasCompactSupport_evenOfflineWaveCos 0 γ hwc)
    (evenOfflineWaveCos_even 0 γ heven) d
  have h4 := primeCrossing_oddPolarWeight_add_oddProfileCollar_eq_mixed a
    (continuous_evenOfflineWaveSin 0 γ hw₀) (hasCompactSupport_evenOfflineWaveSin 0 γ hwc)
    (evenOfflineWaveSin_even 0 γ heven) d
  change primeCrossingWithOddCollar a (evenOfflineWaveCos β γ w₀) d = _ at h1
  change primeCrossingWithOddCollar a (evenOfflineWaveSin β γ w₀) d = _ at h2
  change primeCrossingWithOddCollar a (evenOfflineWaveCos 0 γ w₀) d = _ at h3
  change primeCrossingWithOddCollar a (evenOfflineWaveSin 0 γ w₀) d = _ at h4
  rw [h1, h2, h3, h4]
  have hint (w : ℝ → ℝ) (hw : Continuous w) :
      IntegrableOn (oddProfileCollarMixed a w (Real.log d)) (Ioo (0 : ℝ) (Real.log d)) := by
    unfold oddProfileCollarMixed
    have hpsi := (contDiff_oddPolarFunction (n := 2) a).continuous
    exact (((continuous_riemannKernelReal.mul
      (continuous_riemannKernelReal.comp (continuous_const.sub continuous_id))).mul
      (hpsi.add (hpsi.comp (continuous_const.sub continuous_id)))).mul
      ((hpsi.mul (hw.pow 2)).add
        ((hpsi.comp (continuous_const.sub continuous_id)).mul
          ((hw.comp (continuous_const.sub continuous_id)).pow 2)))).continuousOn.integrableOn_Icc.mono_set
      Ioo_subset_Icc_self
  have hi1 := hint _ (continuous_evenOfflineWaveCos β γ hw₀)
  have hi2 := hint _ (continuous_evenOfflineWaveSin β γ hw₀)
  have hi3 := hint _ (continuous_evenOfflineWaveCos 0 γ hw₀)
  have hi4 := hint _ (continuous_evenOfflineWaveSin 0 γ hw₀)
  have hadd12 := integral_add hi1 hi2
  have hsub123 := integral_sub (hi1.add hi2) hi3
  have hsub1234 := integral_sub ((hi1.add hi2).sub hi3) hi4
  have hcongr :
      (∫ x in Ioo (0 : ℝ) (Real.log d),
        (((oddProfileCollarMixed a (evenOfflineWaveCos β γ w₀) (Real.log d) +
            oddProfileCollarMixed a (evenOfflineWaveSin β γ w₀) (Real.log d)) -
          oddProfileCollarMixed a (evenOfflineWaveCos 0 γ w₀) (Real.log d)) -
          oddProfileCollarMixed a (evenOfflineWaveSin 0 γ w₀) (Real.log d)) x) =
      ∫ x in Ioo (0 : ℝ) (Real.log d),
        oddProfileCollarMixed a (evenOfflineSinhEnvelope β w₀) (Real.log d) x :=
    setIntegral_congr_fun measurableSet_Ioo fun x _ =>
      oddProfileCollarMixed_two_channel_sub_critical_eq a β γ w₀ (Real.log d) x
  linear_combination vonMangoldtAtom d * (hcongr - hsub1234 - hsub123 - hadd12)

theorem primeCrossingWithOddCollar_two_channel_sub_critical_nonneg {a : ℝ} (ha : 0 < a)
    (β γ : ℝ) {w₀ : ℝ → ℝ} (hw₀ : Continuous w₀) (hwc : HasCompactSupport w₀)
    (heven : ∀ x, w₀ (-x) = w₀ x) (d : ℕ) :
    0 ≤ primeCrossingWithOddCollar a (evenOfflineWaveCos β γ w₀) d +
        primeCrossingWithOddCollar a (evenOfflineWaveSin β γ w₀) d -
        primeCrossingWithOddCollar a (evenOfflineWaveCos 0 γ w₀) d -
        primeCrossingWithOddCollar a (evenOfflineWaveSin 0 γ w₀) d := by
  rw [primeCrossingWithOddCollar_two_channel_sub_critical_eq a β γ hw₀ hwc heven d]
  exact mul_nonneg (vonMangoldtAtom_nonneg d)
    (setIntegral_nonneg measurableSet_Ioo fun x hx =>
      oddProfileCollarMixed_nonneg ha hx (evenOfflineSinhEnvelope β w₀))

/-! ## §3. Finite-Packet Off-Diagonal Stationary Positivity Floor and Operator Decompositions -/

/-- Exact Pythagorean norm decomposition on `SourceGraph`:
`‖p‖ ^ 2 = ‖p.val.fst‖ ^ 2 + ‖p.val.snd‖ ^ 2`.
(Classification: Known.) -/
theorem sourceGraph_norm_sq (p : SourceGraph) :
    ‖p‖ ^ (2 : ℕ) = ‖p.val.fst‖ ^ (2 : ℕ) + ‖p.val.snd‖ ^ (2 : ℕ) := by
  rw [← real_inner_self_eq_norm_sq, graph_inner, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq]

/-- Graph-norm bound for `stationaryEnergy`:
for every `p : SourceGraph`, `0 ≤ stationaryEnergy (thetaProduct p.val.fst)` and
`stationaryEnergy (thetaProduct p.val.fst) ≤ (1 + ‖groundPerturbation‖) * ‖p‖ ^ 2`.
(Classification: Known.) -/
theorem stationaryEnergy_nonneg_and_le_sourceGraph_norm_sq (p : SourceGraph) :
    0 ≤ stationaryEnergy (thetaProduct p.val.fst) ∧
      stationaryEnergy (thetaProduct p.val.fst) ≤
        (1 + ‖groundPerturbation‖) * ‖p‖ ^ (2 : ℕ) := by
  have hp : (fullGroundEquiv p).val.fst = p.val.fst := fullGroundEquiv_source p
  have hstat_eq : ⟪(fullGroundEquiv p).val.snd, (fullGroundEquiv p).val.snd⟫_ℝ =
      stationaryEnergy (thetaProduct p.val.fst) := by
    rw [real_inner_self_eq_norm_sq, stationaryGround_edge_energy, hp]
  have hnn : 0 ≤ stationaryEnergy (thetaProduct p.val.fst) := by
    rw [← hstat_eq, real_inner_self_eq_norm_sq]
    exact sq_nonneg _
  have hdecomp := (inner_snd_eq_stationary_add_primeGenerator_add_groundPotential p p).1
  rw [real_inner_self_eq_norm_sq, hstat_eq] at hdecomp
  have hnorm_fst : ‖p.val.fst‖ ^ (2 : ℕ) ≤ ‖p‖ ^ (2 : ℕ) := by
    rw [sourceGraph_norm_sq]; linarith [sq_nonneg ‖p.val.snd‖]
  have hnorm_snd : ‖p.val.snd‖ ^ (2 : ℕ) ≤ ‖p‖ ^ (2 : ℕ) := by
    rw [sourceGraph_norm_sq]; linarith [sq_nonneg ‖p.val.fst‖]
  have hpert : |⟪groundPerturbation p.val.fst, p.val.fst⟫_ℝ| ≤ ‖groundPerturbation‖ * ‖p‖ ^ (2 : ℕ) := by
    calc |⟪groundPerturbation p.val.fst, p.val.fst⟫_ℝ|
        ≤ ‖groundPerturbation p.val.fst‖ * ‖p.val.fst‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖groundPerturbation‖ * ‖p.val.fst‖) * ‖p.val.fst‖ :=
        mul_le_mul_of_nonneg_right (groundPerturbation.le_opNorm p.val.fst) (norm_nonneg _)
      _ = ‖groundPerturbation‖ * ‖p.val.fst‖ ^ (2 : ℕ) := by ring
      _ ≤ ‖groundPerturbation‖ * ‖p‖ ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_left hnorm_fst (norm_nonneg _)
  have hpert_low := neg_le_of_abs_le hpert
  exact ⟨hnn, by linarith⟩

/-- The off-diagonal (`i ≠ j`) Doob `sourcePair` sum of a finite packet `a : ι → SourceGraph`. -/
def packetOffDiagSourcePairSum {ι : Type*} [DecidableEq ι] (S : Finset ι) (a : ι → SourceGraph) : ℝ :=
  ∑ i ∈ S, ∑ j ∈ S.erase i, sourcePair (a i) (a j)

/-- The off-diagonal (`i ≠ j`) stationary edge-pairing sum of a finite packet `a : ι → SourceGraph`. -/
def packetOffDiagStationarySum {ι : Type*} [DecidableEq ι] (S : Finset ι) (a : ι → SourceGraph) : ℝ :=
  ∑ i ∈ S, ∑ j ∈ S.erase i,
    ⟪(fullGroundEquiv (a i)).val.snd, (fullGroundEquiv (a j)).val.snd⟫_ℝ

/-- The off-diagonal (`i ≠ j`) matrix-element sum of a continuous linear operator
`T : MassSpace →L[ℝ] MassSpace` for a finite packet `a : ι → SourceGraph`. -/
def packetOffDiagOperatorSum {ι : Type*} [DecidableEq ι] (T : MassSpace →L[ℝ] MassSpace)
    (S : Finset ι) (a : ι → SourceGraph) : ℝ :=
  ∑ i ∈ S, ∑ j ∈ S.erase i, ⟪T (a i).val.fst, (a j).val.fst⟫_ℝ

theorem fullGroundEquiv_snd_finset_sum {ι : Type*} (S : Finset ι) (a : ι → SourceGraph) :
    (fullGroundEquiv (∑ i ∈ S, a i)).val.snd =
      ∑ i ∈ S, (fullGroundEquiv (a i)).val.snd := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, map_zero]
    rfl
  | @insert k s hk ih =>
    rw [Finset.sum_insert hk, Finset.sum_insert hk, map_add, ← ih]
    rfl

/-- Exact diagonal + off-diagonal expansion of `stationaryEnergy` for a finite packet. -/
theorem packet_stationaryEnergy_sum_eq_diag_add_offDiag {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (a : ι → SourceGraph) :
    stationaryEnergy (thetaProduct (∑ i ∈ S, a i).val.fst) =
      (∑ i ∈ S, stationaryEnergy (thetaProduct (a i).val.fst)) + packetOffDiagStationarySum S a := by
  unfold packetOffDiagStationarySum
  have hstat (p : SourceGraph) :
      stationaryEnergy (thetaProduct p.val.fst) =
        ⟪(fullGroundEquiv p).val.snd, (fullGroundEquiv p).val.snd⟫_ℝ := by
    have hp : (fullGroundEquiv p).val.fst = p.val.fst := fullGroundEquiv_source p
    rw [real_inner_self_eq_norm_sq, stationaryGround_edge_energy, hp]
  rw [hstat (∑ i ∈ S, a i), fullGroundEquiv_snd_finset_sum, sum_inner, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [inner_sum,
    ← Finset.add_sum_erase S
      (fun j => ⟪(fullGroundEquiv (a i)).val.snd, (fullGroundEquiv (a j)).val.snd⟫_ℝ) hi,
    ← hstat (a i)]

/-- Off-diagonal stationary + archimedean + prime-shift decomposition for a finite packet. -/
theorem packetOffDiagSourcePairSum_eq_stationary_sub_arch_sub_primeShift {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (a : ι → SourceGraph) :
    packetOffDiagSourcePairSum S a =
      packetOffDiagStationarySum S a -
        packetOffDiagOperatorSum archDiagonalOperator S a -
        packetOffDiagOperatorSum primeShiftOperator S a := by
  unfold packetOffDiagSourcePairSum packetOffDiagStationarySum packetOffDiagOperatorSum
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sourcePair_eq_stationary_sub_arch_sub_primeShift (a i) (a j),
    inner_archDiagonalOperator]

/-- **Universal Off-Diagonal Stationary Positivity Floor (`packetOffDiagStationarySum_ge_neg_diag`):**
Because the total stationary energy `stationaryEnergy (thetaProduct (∑ i ∈ S, a i).val.fst)` of any
finite packet $a : \iota \to \operatorname{SourceGraph}$ is non-negative, its off-diagonal
stationary sum is bounded below by the negative of the diagonal stationary sum, and hence by
$-(1 + \|\operatorname{groundPerturbation}\|) \sum_{i \in S} \|a_i\|^2$.
(Classification: Candidate new theorem.) -/
theorem packetOffDiagStationarySum_ge_neg_diag {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (a : ι → SourceGraph) :
    -(∑ i ∈ S, stationaryEnergy (thetaProduct (a i).val.fst)) ≤ packetOffDiagStationarySum S a ∧
      -((1 + ‖groundPerturbation‖) * ∑ i ∈ S, ‖a i‖ ^ (2 : ℕ)) ≤ packetOffDiagStationarySum S a := by
  have htot : 0 ≤ stationaryEnergy (thetaProduct (∑ i ∈ S, a i).val.fst) :=
    (stationaryEnergy_nonneg_and_le_sourceGraph_norm_sq (∑ i ∈ S, a i)).1
  have hsplit := packet_stationaryEnergy_sum_eq_diag_add_offDiag S a
  have hdiag : (∑ i ∈ S, stationaryEnergy (thetaProduct (a i).val.fst)) ≤
      (1 + ‖groundPerturbation‖) * ∑ i ∈ S, ‖a i‖ ^ (2 : ℕ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => (stationaryEnergy_nonneg_and_le_sourceGraph_norm_sq (a i)).2
  exact ⟨by linarith, by linarith⟩

/-- **Off-Diagonal `sourcePair` Lower Bound via Stationary Positivity
(`packetOffDiagSourcePairSum_ge_neg_diag_sub_arch_sub_primeShift`):**
For any finite packet $a : \iota \to \operatorname{SourceGraph}$, the off-diagonal Doob pairing sum
is bounded below by the negative off-diagonal archimedean and prime-shift operator sums minus the
diagonal graph cost $(1 + \|\operatorname{groundPerturbation}\|)\sum_{i \in S} \|a_i\|^2$.
(Classification: Corollary.) -/
theorem packetOffDiagSourcePairSum_ge_neg_diag_sub_arch_sub_primeShift {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (a : ι → SourceGraph) :
    -((1 + ‖groundPerturbation‖) * ∑ i ∈ S, ‖a i‖ ^ (2 : ℕ)) -
        packetOffDiagOperatorSum archDiagonalOperator S a -
        packetOffDiagOperatorSum primeShiftOperator S a ≤
      packetOffDiagSourcePairSum S a := by
  have hdecomp := packetOffDiagSourcePairSum_eq_stationary_sub_arch_sub_primeShift S a
  have hstat := (packetOffDiagStationarySum_ge_neg_diag S a).2
  linarith

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
