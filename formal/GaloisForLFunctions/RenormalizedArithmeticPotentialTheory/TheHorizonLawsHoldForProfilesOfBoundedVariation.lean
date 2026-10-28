import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheFinitePartIsEulersConstant
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheHorizonCountertermIsATensorProduct
import Mathlib.Topology.EMetricSpace.BoundedVariation

/-!
# The horizon laws hold for profiles of bounded variation

The horizon laws — polarity (`abs_atomicWeilForm_stepProfile_sub_le`), the finite part `−2γ`
(`exists_abs_atomicWeilForm_stepProfile_finitePart_le`) and the tensor law on the `p`-adic classes
(`abs_atomicWeilForm_classProfile_sub_le`) — are stated on step profiles, with errors measured by
the absolute coefficients. Every vector is a step profile. Summation by parts gives
`G(n) n^{−1/2} = Σ_{n ≤ m ≤ N} ∂G(m) u^{(m)}_n` on `[1, N]`, with `∂G(m) = G(m) − G(m + 1)` and
`∂G(N) = G(N)` (`stepProfile_horizonDiff`). The absolute coefficient mass is the **horizon
variation** `V_N(G) = Σ_{m ≤ N} |∂G(m)|`.

* **Every profile** (`abs_atomicWeilForm_profile_sub_le`,
  `exists_abs_atomicWeilForm_profile_finitePart_le`): for `x_n = G(n) n^{−1/2}`,
  `|P_N(x) − ℓ(x)²| ≤ (log 8 + 5) H_N V_N(G)²`, and for every `η > 0`,
  `|P_N(x) − ℓ(x)² + 2γ|x|²| ≤ (η H_N + C_η) V_N(G)²`.
* **Every class-wise profile** (`abs_atomicWeilForm_classwiseProfile_sub_le`): for
  `x_n = G_{v_p(n)}(n) n^{−1/2}` on the classes `v_p(n) ≤ J`,
  `|P_N(x) − Σ_j δ_j^{−1} ℓ_j(x)²| ≤ C_{p,J} H_N (Σ_j V_N(G_j))²`.
* **Profiles of bounded variation** (`horizonVariation_le`,
  `exists_abs_atomicWeilForm_bv_finitePart_le`, `abs_atomicWeilForm_bv_classwise_sub_le`): for
  `G(n) = g(log n/log N)` with `g` of bounded variation on `[0, 1]`,
  `V_N(G) ≤ Var_{[0,1]} g + |g(1)|` uniformly in `N`, because the points `log n/log N` partition
  `[0, 1]`. So `P_N(x) = ℓ(x)² − 2γ|x|² + o(log N)`, and on signed class profiles at fixed `p, J`,
  `P_N(x) = Σ_j δ_j^{−1} ℓ_j(x)² + O(log N)`.

For a fixed profile `g` the divergence `ℓ²` is of order `(log N)²` and the mass `|x|²` of order
`log N`. The laws therefore determine the horizon form of every signed profile of bounded variation,
smooth ones included, up to `o(mass)`: the restriction to step profiles was a convenience.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.Moebius

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticFunction GaloisForLFunctions.ArithmeticEffectivityTheory
  GaloisForLFunctions.ArithmeticElectrostatics

local notation "γ" => Real.eulerMascheroniConstant

variable {p : ℕ}

/-! ### Summation by parts at the horizon -/

/-- The **horizon difference** `∂G(m) = G(m) − G(m + 1)` for `m < N`, and `∂G(N) = G(N)`. -/
def horizonDiff (G : ℕ → ℝ) (N m : ℕ) : ℝ := G m - if m < N then G (m + 1) else 0

/-- The **horizon variation** `V_N(G) = Σ_{m ≤ N} |∂G(m)|`. -/
def horizonVariation (G : ℕ → ℝ) (N : ℕ) : ℝ := ∑ m ∈ Icc 1 N, |horizonDiff G N m|

theorem horizonVariation_nonneg (G : ℕ → ℝ) (N : ℕ) : 0 ≤ horizonVariation G N :=
  sum_nonneg fun _ _ => abs_nonneg _

/-- Telescoping: `Σ_{n ≤ m ≤ N} ∂G(m) = G(n)`. -/
theorem sum_horizonDiff (G : ℕ → ℝ) {n N : ℕ} (hnN : n ≤ N) :
    ∑ m ∈ Icc n N, horizonDiff G N m = G n := by
  induction N, hnN using Nat.le_induction with
  | base => simp [horizonDiff]
  | succ N hN ih =>
    have h : ∀ m ∈ Icc n N, horizonDiff G (N + 1) m =
        horizonDiff G N m - if m = N then G (N + 1) else 0 := by
      intro m hm
      have hmN := (mem_Icc.mp hm).2
      unfold horizonDiff
      by_cases hm' : m = N
      · subst hm'
        simp
      · have hlt : m < N := lt_of_le_of_ne hmN hm'
        simp [hlt, hm', show m < N + 1 by omega]
    rw [sum_Icc_succ_top (by omega), sum_congr rfl h, sum_sub_distrib, ih, sum_ite_eq']
    simp [horizonDiff, mem_Icc.mpr ⟨hN, le_rfl⟩]

theorem sum_range_add_one_eq_sum_Icc (f : ℕ → ℝ) (N : ℕ) :
    ∑ i ∈ range N, f (i + 1) = ∑ m ∈ Icc 1 N, f m := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih, sum_Icc_succ_top (by omega)]

/-- **Every profile is a step profile**: on `[1, N]`,
`G(n) n^{−1/2} = Σ_{i < N} ∂G(i + 1) u^{(i + 1)}_n`. -/
theorem stepProfile_horizonDiff (G : ℕ → ℝ) {N n : ℕ} (hn : n ∈ Icc 1 N) :
    stepProfile (fun i : Fin N => horizonDiff G N (i + 1)) (fun i : Fin N => (i : ℕ) + 1) n =
      G n * poleVector n := by
  have hnN := (mem_Icc.mp hn).2
  simp only [stepProfile]
  rw [Fin.sum_univ_eq_sum_range (fun i => horizonDiff G N (i + 1) * truncPole (i + 1) n) N,
    sum_range_add_one_eq_sum_Icc (fun m => horizonDiff G N m * truncPole m n)]
  simp only [truncPole, mul_ite, mul_zero]
  rw [← sum_filter]
  have hfilt : (Icc 1 N).filter (fun m => n ≤ m) = Icc n N := by
    ext m
    simp only [mem_filter, mem_Icc]
    have := (mem_Icc.mp hn).1
    omega
  rw [hfilt, ← sum_mul, sum_horizonDiff G hnN]

theorem sum_abs_horizonDiff (G : ℕ → ℝ) (N : ℕ) :
    ∑ i : Fin N, |horizonDiff G N (i + 1)| = horizonVariation G N := by
  rw [Fin.sum_univ_eq_sum_range (fun i => |horizonDiff G N (i + 1)|) N,
    sum_range_add_one_eq_sum_Icc (fun m => |horizonDiff G N m|), horizonVariation]

theorem atomicWeilForm_congr {N : ℕ} {x y : ℕ → ℝ} (h : ∀ n ∈ Icc 1 N, x n = y n) :
    atomicWeilForm N x = atomicWeilForm N y := by
  unfold atomicWeilForm
  exact sum_congr rfl fun m hm => sum_congr rfl fun n hn => by rw [h m hm, h n hn]

theorem polarFunctional_congr {N : ℕ} {x y : ℕ → ℝ} (h : ∀ n ∈ Icc 1 N, x n = y n) :
    polarFunctional N x = polarFunctional N y :=
  sum_congr rfl fun n hn => by rw [h n hn]

/-- The step-profile mass is at most `H_N (Σ_i |c_i|)²`. -/
theorem sum_abs_mul_harmonicSum_min_le {k N : ℕ} (c : Fin k → ℝ) (M : Fin k → ℕ)
    (hM : ∀ i, M i ≤ N) :
    ∑ i, ∑ j, |c i| * |c j| * harmonicSum (min (M i) (M j)) ≤
      harmonicSum N * (∑ i, |c i|) ^ 2 := by
  rw [sq, sum_mul_sum, mul_sum]
  refine sum_le_sum fun i _ => ?_
  rw [mul_sum]
  refine sum_le_sum fun j _ => ?_
  have hH := harmonicSum_mono ((min_le_left (M i) (M j)).trans (hM i))
  calc |c i| * |c j| * harmonicSum (min (M i) (M j)) ≤ |c i| * |c j| * harmonicSum N :=
        mul_le_mul_of_nonneg_left hH (by positivity)
    _ = harmonicSum N * (|c i| * |c j|) := by ring

/-! ### The laws for every profile -/

/-- **Polarity for every profile**: `x_n = G(n) n^{−1/2}` has
`|P_N(x) − ℓ(x)²| ≤ (log 8 + 5) H_N V_N(G)²`. -/
theorem abs_atomicWeilForm_profile_sub_le (G : ℕ → ℝ) (N : ℕ) :
    |atomicWeilForm N (fun n => G n * poleVector n) -
        polarFunctional N (fun n => G n * poleVector n) ^ 2| ≤
      (Real.log 8 + 5) * harmonicSum N * horizonVariation G N ^ 2 := by
  have hM : ∀ i : Fin N, (fun i : Fin N => (i : ℕ) + 1) i ≤ N := fun i => Nat.succ_le_of_lt i.2
  have hx : ∀ n ∈ Icc 1 N, G n * poleVector n =
      stepProfile (fun i : Fin N => horizonDiff G N (i + 1)) (fun i : Fin N => (i : ℕ) + 1) n :=
    fun n hn => (stepProfile_horizonDiff G hn).symm
  have h8 : 0 ≤ Real.log 8 + 5 := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 8)
    linarith
  rw [atomicWeilForm_congr hx, polarFunctional_congr hx, ← sum_abs_horizonDiff, mul_assoc]
  exact (abs_atomicWeilForm_stepProfile_sub_le _ _ hM).trans
    (mul_le_mul_of_nonneg_left (sum_abs_mul_harmonicSum_min_le _ _ hM) h8)

/-- **The finite part for every profile**: for every `η > 0` there is `C` with
`|P_N(x) − ℓ(x)² + 2γ|x|²| ≤ (η H_N + C) V_N(G)²` for `x_n = G(n) n^{−1/2}`. -/
theorem exists_abs_atomicWeilForm_profile_finitePart_le {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, ∀ (N : ℕ) (G : ℕ → ℝ),
      |atomicWeilForm N (fun n => G n * poleVector n) -
          polarFunctional N (fun n => G n * poleVector n) ^ 2 +
          2 * γ * ∑ n ∈ Icc 1 N, (G n * poleVector n) ^ 2| ≤
        (η * harmonicSum N + C) * horizonVariation G N ^ 2 := by
  obtain ⟨C, hC⟩ := exists_abs_atomicWeilForm_stepProfile_finitePart_le hη
  refine ⟨|C|, fun N G => ?_⟩
  set c : Fin N → ℝ := fun i => horizonDiff G N (i + 1)
  set M : Fin N → ℕ := fun i => (i : ℕ) + 1
  have hM : ∀ i, M i ≤ N := fun i => Nat.succ_le_of_lt i.2
  have hM1 : ∀ i, 1 ≤ M i := fun i => Nat.le_add_left 1 _
  have hx : ∀ n ∈ Icc 1 N, G n * poleVector n = stepProfile c M n := fun n hn =>
    (stepProfile_horizonDiff G hn).symm
  have hsq : ∑ n ∈ Icc 1 N, (G n * poleVector n) ^ 2 = ∑ n ∈ Icc 1 N, stepProfile c M n ^ 2 :=
    sum_congr rfl fun n hn => by rw [hx n hn]
  rw [atomicWeilForm_congr hx, polarFunctional_congr hx, hsq, ← sum_abs_horizonDiff]
  refine (hC c M hM1 hM).trans ?_
  rw [sq, sum_mul_sum, mul_sum]
  refine sum_le_sum fun i _ => ?_
  rw [mul_sum]
  refine sum_le_sum fun j _ => ?_
  have hH := harmonicSum_mono ((min_le_left (M i) (M j)).trans (hM i))
  have hle : η * harmonicSum (min (M i) (M j)) + C ≤ η * harmonicSum N + |C| := by
    have := mul_le_mul_of_nonneg_left hH hη.le
    linarith [le_abs_self C]
  calc |c i| * |c j| * (η * harmonicSum (min (M i) (M j)) + C)
      ≤ |c i| * |c j| * (η * harmonicSum N + |C|) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = (η * harmonicSum N + |C|) * (|c i| * |c j|) := by ring

/-- The **class-wise profile** `x_n = G_{v_p(n)}(n) n^{−1/2}` on the classes `v_p(n) ≤ J`. -/
def classwiseProfile (p J : ℕ) (G : Fin (J + 1) → ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ j : Fin (J + 1), if n.factorization p = j then G j n * poleVector n else 0

theorem classProfile_horizonDiff (p J : ℕ) (G : Fin (J + 1) → ℕ → ℝ) {N n : ℕ}
    (hn : n ∈ Icc 1 N) :
    classProfile p (fun a : Fin (J + 1) × Fin N => horizonDiff (G a.1) N (a.2 + 1))
        (fun i : Fin N => (i : ℕ) + 1) n = classwiseProfile p J G n := by
  rw [classProfile, Fintype.sum_prod_type, classwiseProfile]
  refine sum_congr rfl fun j _ => ?_
  simp only [classPole]
  by_cases hj : n.factorization p = j
  · simp only [if_pos hj]
    exact stepProfile_horizonDiff (G j) hn
  · simp [hj]

/-- **The tensor law for every class-wise profile**:
`|P_N(x) − Σ_j δ_j^{−1} ℓ_j(x)²| ≤ C_{p,J} H_N (Σ_j V_N(G_j))²`. -/
theorem abs_atomicWeilForm_classwiseProfile_sub_le (hp : p.Prime) (J : ℕ)
    (G : Fin (J + 1) → ℕ → ℝ) (N : ℕ) :
    |atomicWeilForm N (classwiseProfile p J G) -
        ∑ j : Fin (J + 1), classPolar p j N (classwiseProfile p J G) ^ 2 / classDensity p j| ≤
      tensorConstant p J * harmonicSum N * (∑ j, horizonVariation (G j) N) ^ 2 := by
  set c : Fin (J + 1) × Fin N → ℝ := fun a => horizonDiff (G a.1) N (a.2 + 1)
  set M : Fin N → ℕ := fun i => (i : ℕ) + 1
  have hM : ∀ i, M i ≤ N := fun i => Nat.succ_le_of_lt i.2
  have hx : ∀ n ∈ Icc 1 N, classwiseProfile p J G n = classProfile p c M n := fun n hn =>
    (classProfile_horizonDiff p J G hn).symm
  have hpolar : ∀ j : Fin (J + 1), classPolar p j N (classwiseProfile p J G) =
      classPolar p j N (classProfile p c M) := fun j =>
    sum_congr rfl fun n hn => by rw [hx n hn]
  have hvar : ∑ a, |c a| = ∑ j, horizonVariation (G j) N := by
    rw [Fintype.sum_prod_type]
    exact sum_congr rfl fun j _ => sum_abs_horizonDiff (G j) N
  rw [atomicWeilForm_congr hx]
  simp_rw [hpolar]
  rw [← hvar]
  exact abs_atomicWeilForm_classProfile_sub_le hp c M hM

/-! ### Profiles of bounded variation -/

/-- **The horizon variation of a profile of bounded variation**: for `N ≥ 2`,
`V_N(g(log · /log N)) ≤ Var_{[0,1]} g + |g(1)|`. -/
theorem horizonVariation_le {g : ℝ → ℝ} (hg : BoundedVariationOn g (Set.Icc 0 1)) {N : ℕ}
    (hN : 2 ≤ N) :
    horizonVariation (fun n => g (Real.log n / Real.log N)) N ≤
      (eVariationOn g (Set.Icc 0 1)).toReal + |g 1| := by
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  -- split off the top term `|G(N)| = |g(1)|`
  have hsplit : horizonVariation (fun n => g (Real.log n / Real.log N)) N =
      ∑ m ∈ Ico 1 N, |g (Real.log m / Real.log N) - g (Real.log (m + 1 : ℕ) / Real.log N)| +
        |g 1| := by
    rw [horizonVariation, ← Finset.Ico_insert_right (by omega : 1 ≤ N), sum_insert (by simp),
      add_comm]
    congr 1
    · exact sum_congr rfl fun m hm => by rw [horizonDiff, if_pos (mem_Ico.mp hm).2]
    · rw [horizonDiff, if_neg (lt_irrefl N), sub_zero, div_self hlogN.ne']
  -- the points `log m/log N` partition `[0, 1]`
  have hmono : MonotoneOn (fun m : ℕ => Real.log m / Real.log N) (Set.Icc 1 N) := by
    intro a ha b _ hab
    have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha.1
    exact div_le_div_of_nonneg_right (Real.log_le_log (by linarith) (by exact_mod_cast hab))
      hlogN.le
  have hmem : ∀ m ∈ Set.Icc 1 N, Real.log m / Real.log N ∈ Set.Icc (0 : ℝ) 1 := by
    intro m hm
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm.1
    refine ⟨div_nonneg (Real.log_nonneg hm1) hlogN.le, (div_le_one hlogN).mpr ?_⟩
    exact Real.log_le_log (by linarith) (by exact_mod_cast hm.2)
  have h := eVariationOn.sum_le_of_monotoneOn_Icc (f := g) hmono hmem
  have hsum : ∑ m ∈ Ico 1 N, |g (Real.log m / Real.log N) - g (Real.log (m + 1 : ℕ) / Real.log N)|
      ≤ (eVariationOn g (Set.Icc 0 1)).toReal := by
    rw [← ENNReal.ofReal_le_iff_le_toReal hg, ENNReal.ofReal_sum_of_nonneg
      (fun _ _ => abs_nonneg _)]
    refine le_trans (sum_le_sum fun m _ => ?_) h
    rw [edist_dist, Real.dist_eq, abs_sub_comm]
  rw [hsplit]
  linarith

/-- **The finite part for profiles of bounded variation**: for `g` of bounded variation on `[0, 1]`
and every `η > 0` there is `C` with `|P_N(x) − ℓ(x)² + 2γ|x|²| ≤ η log N + C` for
`x_n = g(log n/log N) n^{−1/2}`, `N ≥ 2`. -/
theorem exists_abs_atomicWeilForm_bv_finitePart_le {g : ℝ → ℝ}
    (hg : BoundedVariationOn g (Set.Icc 0 1)) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      |atomicWeilForm N (fun n => g (Real.log n / Real.log N) * poleVector n) -
          polarFunctional N (fun n => g (Real.log n / Real.log N) * poleVector n) ^ 2 +
          2 * γ * ∑ n ∈ Icc 1 N, (g (Real.log n / Real.log N) * poleVector n) ^ 2| ≤
        η * Real.log N + C := by
  set V := (eVariationOn g (Set.Icc 0 1)).toReal + |g 1| with hVdef
  have hV : 0 ≤ V := add_nonneg ENNReal.toReal_nonneg (abs_nonneg _)
  have hη' : 0 < η / (V ^ 2 + 1) := by positivity
  obtain ⟨C, hC⟩ := exists_abs_atomicWeilForm_profile_finitePart_le hη'
  refine ⟨η + |C| * V ^ 2, fun N hN => ?_⟩
  have h := hC N fun n => g (Real.log n / Real.log N)
  have hW := horizonVariation_le hg hN
  have hW0 := horizonVariation_nonneg (fun n => g (Real.log n / Real.log N)) N
  have hH0 := harmonicSum_nonneg N
  have hH := harmonicSum_le N
  have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hηV : η / (V ^ 2 + 1) * V ^ 2 ≤ η := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  refine h.trans ?_
  calc (η / (V ^ 2 + 1) * harmonicSum N + C) *
        horizonVariation (fun n => g (Real.log n / Real.log N)) N ^ 2
      ≤ (η / (V ^ 2 + 1) * harmonicSum N + |C|) *
          horizonVariation (fun n => g (Real.log n / Real.log N)) N ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith [le_abs_self C]) (sq_nonneg _)
    _ ≤ (η / (V ^ 2 + 1) * harmonicSum N + |C|) * V ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hW0 hW 2) (by positivity)
    _ = η / (V ^ 2 + 1) * V ^ 2 * harmonicSum N + |C| * V ^ 2 := by ring
    _ ≤ η * (1 + Real.log N) + |C| * V ^ 2 := by
        have := mul_le_mul hηV hH hH0 hη.le
        linarith
    _ = η * Real.log N + (η + |C| * V ^ 2) := by ring

theorem tensorConstant_nonneg (hp : p.Prime) (J : ℕ) : 0 ≤ tensorConstant p J := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hc : 0 < 1 - 1 / (p : ℝ) := by rw [sub_pos, div_lt_one (by linarith)]; exact hp1
  have h1 : 0 ≤ Real.log p / ((p : ℝ) - 1) := div_nonneg (Real.log_nonneg hp1.le) (by linarith)
  have h2 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
  have h3 : 0 ≤ Real.log p := Real.log_nonneg hp1.le
  unfold tensorConstant
  positivity

/-- **The tensor law for signed class profiles of bounded variation**: for `g_j` of bounded
variation on `[0, 1]` and `N ≥ 2`, the profile `x_n = g_{v_p(n)}(log n/log N) n^{−1/2}` has
`|P_N(x) − Σ_j δ_j^{−1} ℓ_j(x)²| ≤ C_{p,J} (1 + log N) (Σ_j (Var g_j + |g_j(1)|))²`. -/
theorem abs_atomicWeilForm_bv_classwise_sub_le (hp : p.Prime) (J : ℕ)
    {g : Fin (J + 1) → ℝ → ℝ} (hg : ∀ j, BoundedVariationOn (g j) (Set.Icc 0 1)) {N : ℕ}
    (hN : 2 ≤ N) :
    |atomicWeilForm N (classwiseProfile p J fun j n => g j (Real.log n / Real.log N)) -
        ∑ j : Fin (J + 1), classPolar p j N
          (classwiseProfile p J fun j n => g j (Real.log n / Real.log N)) ^ 2 /
            classDensity p j| ≤
      tensorConstant p J * (1 + Real.log N) *
        (∑ j, ((eVariationOn (g j) (Set.Icc 0 1)).toReal + |g j 1|)) ^ 2 := by
  refine (abs_atomicWeilForm_classwiseProfile_sub_le hp J _ N).trans ?_
  have hC0 := tensorConstant_nonneg hp J
  have hS0 : 0 ≤ ∑ j, horizonVariation (fun n => g j (Real.log n / Real.log N)) N :=
    sum_nonneg fun j _ => horizonVariation_nonneg _ N
  exact mul_le_mul (mul_le_mul_of_nonneg_left (harmonicSum_le N) hC0)
    (pow_le_pow_left₀ hS0 (sum_le_sum fun j _ => horizonVariation_le (hg j) hN) 2)
    (sq_nonneg _) (by have := Real.log_natCast_nonneg N; positivity)

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
