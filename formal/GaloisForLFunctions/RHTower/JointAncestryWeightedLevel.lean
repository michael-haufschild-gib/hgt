import GaloisForLFunctions.RHTower.JointAncestryWeightedBochner

/-!
# Dressed product positivity at level `σ` forces `|Re ρ − ½| ≤ max(0, σ − 1)`

For every dressing `g`, the argument of `JointAncestryDiagonalBochnerLevel` runs with the dressed
lag function `Φ_g`:
* the dressed diagonal Bochner bound controls the weighted window average of `Φ_g(log p)`;
* coherence of `Φ_g` (`abs_dLagReal_add_sub_le`) replaces `Φ_g(log p)` by `Φ_g(u)`;
* the dressed growth criterion (`re_le_half_add_of_dLagReal_le_exp`) converts the resulting bound
  `|Φ_g(u)| = O(e^{max(c, α − min(c, δ/4))u})` into `α ≤ c`.

**Theorems.** `abs_re_sub_half_le_of_jasWeightedProductPositiveAbove D`: dressed positivity at level
`σ ≥ 0` on the primes `p > X` gives `|Re ρ − ½| ≤ max(0, σ − 1)`.
`riemannHypothesis_iff_exists_jasWeightedProductPositiveAbove_one`: for a dressing positive on the
critical line, `RH ⟺ ∃ X, dressed positivity at level 1 on the primes p > X`.
-/

open Complex Filter
open scoped ComplexConjugate

namespace RHTower

noncomputable section

variable (D : LagDressing)

/-- **Dressed interval positivity.** -/
def JasWeightedIntervalPositive (X : ℕ) (σ : ℝ) : Prop :=
  ∀ y L : ℝ, (X : ℝ) + 1 ≤ y → 0 ≤ L → JasWeightedConstPositiveOn D (jasIntervalPrimes y L) σ

theorem JasWeightedProductPositiveAbove.intervalPositive {D : LagDressing} {X : ℕ} {σ : ℝ}
    (h : JasWeightedProductPositiveAbove D X σ) : JasWeightedIntervalPositive D X σ := by
  intro y L hy _
  refine h.constOn fun p hp => ?_
  have hp' : (p : ℕ) ∈ (Finset.Ioc ⌊y⌋₊ ⌊y + L⌋₊).filter Nat.Prime := Finset.mem_subtype.mp hp
  rw [Finset.mem_filter, Finset.mem_Ioc] at hp'
  have h1 : y < ((p : ℕ) : ℝ) := (Nat.floor_lt (by linarith [Nat.cast_nonneg (α := ℝ) X])).mp hp'.1.1
  have : (X : ℝ) < ((p : ℕ) : ℝ) := by linarith
  exact_mod_cast this

theorem abs_dLagReal_le_of_window {σ : ℝ}
    {α δ c u : ℝ} (hα : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ α)
    (hδ0 : 0 < δ) (hu1 : 1 ≤ u) (hE4 : 4 * Real.exp (-(c * u)) ≤ 1)
    (P : Finset Nat.Primes) (hpos : JasWeightedConstPositiveOn D P σ)
    (hlogP' : ∀ p ∈ P, u ≤ Real.log ((p : ℕ) : ℝ) ∧ Real.log ((p : ℕ) : ℝ) ≤ u + Real.exp (-(δ * u)))
    (hMass : Real.exp (-(c * u)) ≤ ∑ p ∈ P, Real.exp (-σ * Real.log ((p : ℕ) : ℝ))) :
    |dLagReal D u| ≤ 2 * |dLagReal D 0| * Real.exp (c * u) +
      32 * D.total * (Real.exp (-(c * u)) + Real.exp ((α - c) * u)) +
        D.K * (Real.exp (α * u) * diagCoherence δ u) := by
  obtain ⟨h, hh⟩ : ∃ h : ℝ, h = Real.exp (-(δ * u)) := ⟨_, rfl⟩
  have hu0 : 0 ≤ u := by linarith
  have hh0 : 0 < h := by rw [hh]; exact Real.exp_pos _
  have hh1 : h ≤ 1 := by rw [hh]; exact Real.exp_le_one_iff.mpr (by nlinarith)
  have hlogP : ∀ p ∈ P, u ≤ Real.log ((p : ℕ) : ℝ) ∧ Real.log ((p : ℕ) : ℝ) ≤ u + h := by
    rw [hh]; exact hlogP'
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = ∑ p ∈ P, Real.exp (-σ * Real.log ((p : ℕ) : ℝ)) := ⟨_, rfl⟩
  rw [← hMdef] at hMass
  have hM0 : 0 < M := lt_of_lt_of_le (Real.exp_pos _) hMass
  -- the weights
  obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = Real.exp (-(c * u)) / M := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hrdef]; exact div_pos (Real.exp_pos _) hM0
  have hr1 : r ≤ 1 := by rw [hrdef, div_le_one hM0]; exact hMass
  have hS : ∑ p ∈ P, diagA σ r p = r / (1 + r ^ 2) * M := by
    rw [hMdef, Finset.mul_sum]; rfl
  have hrM : r * M = Real.exp (-(c * u)) := by rw [hrdef]; field_simp
  have hSlow : Real.exp (-(c * u)) / 2 ≤ ∑ p ∈ P, diagA σ r p := by
    rw [hS, ← hrM]
    have h1 : 1 + r ^ 2 ≤ 2 := by nlinarith
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith
  have hSup : ∑ p ∈ P, diagA σ r p ≤ Real.exp (-(c * u)) := by
    rw [hS, ← hrM, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg hr0.le hM0.le) (sq_nonneg r)]
  -- the Bochner bound
  have hstar := abs_sum_dLagReal_le_of_weightedConstPositive D hα hu0 hr0.le P hpos hlogP
  have hK : ∑ p ∈ P, 2 * (diagA σ r p * Real.exp (h / 2)) ≤ 4 * Real.exp (-(c * u)) := by
    rw [← Finset.mul_sum, ← Finset.sum_mul]
    have he : Real.exp (h / 2) ≤ 2 :=
      (Real.exp_le_exp.mpr (by linarith)).trans exp_one_half_le_two_lag
    have hS0 : 0 ≤ ∑ p ∈ P, diagA σ r p := Finset.sum_nonneg fun p _ => diagA_nonneg hr0.le p
    have := mul_le_mul hSup he (Real.exp_pos _).le (Real.exp_pos _).le
    linarith
  obtain ⟨x, hxdef⟩ : ∃ x : Nat.Primes → ℝ, x = fun p => 2 * (diagA σ r p * Real.exp (h / 2)) :=
    ⟨_, rfl⟩
  have hx0 : ∀ p ∈ P, 0 ≤ x p := fun p _ => by
    rw [hxdef]; exact mul_nonneg (by norm_num) (mul_nonneg (diagA_nonneg hr0.le p) (Real.exp_pos _).le)
  have hxs : ∑ p ∈ P, x p ≤ 4 * Real.exp (-(c * u)) := by rw [hxdef]; exact hK
  have hR : (∏ p ∈ P, (1 + 2 * (diagA σ r p * Real.exp (h / 2)))) - 1 -
      2 * ∑ p ∈ P, diagA σ r p * Real.exp (h / 2) ≤ 16 * Real.exp (-(c * u)) ^ 2 := by
    have h1 := prod_one_add_sub_le_sq P x hx0 (hxs.trans hE4)
    have e1 : ∏ p ∈ P, (1 + 2 * (diagA σ r p * Real.exp (h / 2))) = ∏ p ∈ P, (1 + x p) := by
      rw [hxdef]
    have e2 : 2 * ∑ p ∈ P, diagA σ r p * Real.exp (h / 2) = ∑ p ∈ P, x p := by
      rw [hxdef, Finset.mul_sum]
    rw [e1, e2]
    have hx00 : 0 ≤ ∑ p ∈ P, x p := Finset.sum_nonneg hx0
    have h2 : (∑ p ∈ P, x p) ^ 2 ≤ (4 * Real.exp (-(c * u))) ^ 2 := pow_le_pow_left₀ hx00 hxs 2
    calc (∏ p ∈ P, (1 + x p)) - 1 - ∑ p ∈ P, x p ≤ (∑ p ∈ P, x p) ^ 2 := h1
      _ ≤ (4 * Real.exp (-(c * u))) ^ 2 := h2
      _ = 16 * Real.exp (-(c * u)) ^ 2 := by ring
  -- coherence
  have hcoh : ∀ p ∈ P, |dLagReal D (Real.log ((p : ℕ) : ℝ)) - dLagReal D u| ≤
      D.K * (Real.exp (α * u) * diagCoherence δ u) := by
    intro p hp
    obtain ⟨h1, h2⟩ := hlogP p hp
    have hT : 1 ≤ Real.exp (δ * u / 2) := Real.one_le_exp (by positivity)
    have := abs_dLagReal_add_sub_le D hα hu0 (sub_nonneg.mpr h1) (by linarith) hT
      (y := Real.log ((p : ℕ) : ℝ) - u)
    rw [show u + (Real.log ((p : ℕ) : ℝ) - u) = Real.log ((p : ℕ) : ℝ) by ring] at this
    refine this.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le) D.K_nonneg)
    unfold diagCoherence
    have hW := lagWeightTotal_nonneg
    have he := Real.exp_pos (1 / 2 : ℝ)
    gcongr
    rw [← hh]
    linarith
  -- assemble
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = ∑ p ∈ P, diagA σ r p := ⟨_, rfl⟩
  rw [← hSdef] at hSlow hSup
  have hS0 : 0 < S := lt_of_lt_of_le (by positivity) hSlow
  have hsplit : S * |dLagReal D u| ≤
      |∑ p ∈ P, diagA σ r p * dLagReal D (Real.log ((p : ℕ) : ℝ))| +
        S * (D.K * (Real.exp (α * u) * diagCoherence δ u)) := by
    have e : S * dLagReal D u = ∑ p ∈ P, diagA σ r p * dLagReal D (Real.log ((p : ℕ) : ℝ)) -
        ∑ p ∈ P, diagA σ r p * (dLagReal D (Real.log ((p : ℕ) : ℝ)) - dLagReal D u) := by
      rw [hSdef, Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun p _ => by ring
    rw [← abs_of_pos hS0, ← abs_mul, e]
    refine (abs_sub _ _).trans (add_le_add le_rfl ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [abs_of_pos hS0, hSdef, Finset.sum_mul]
    refine Finset.sum_le_sum fun p hp => ?_
    rw [abs_mul, abs_of_nonneg (diagA_nonneg hr0.le p)]
    exact mul_le_mul_of_nonneg_left (hcoh p hp) (diagA_nonneg hr0.le p)
  have hA0 : 0 ≤ |dLagReal D 0| + D.total * (16 * Real.exp (-(c * u)) ^ 2) *
      (1 + Real.exp (α * u)) := by
    have := D.total_nonneg; positivity
  have hstar' : |∑ p ∈ P, diagA σ r p * dLagReal D (Real.log ((p : ℕ) : ℝ))| ≤
      |dLagReal D 0| + D.total * (16 * Real.exp (-(c * u)) ^ 2) *
        (1 + Real.exp (α * u)) := by
    refine hstar.trans ?_
    have := le_abs_self (dLagReal D 0)
    have := D.total_nonneg
    have := Real.exp_pos (α * u)
    gcongr
  have hdiv : |dLagReal D u| ≤ (|dLagReal D 0| + D.total *
      (16 * Real.exp (-(c * u)) ^ 2) * (1 + Real.exp (α * u))) / S +
        D.K * (Real.exp (α * u) * diagCoherence δ u) := by
    rw [div_add' _ _ _ hS0.ne', le_div_iff₀ hS0]
    linarith [hsplit, hstar']
  have hinv : 1 / S ≤ 2 * Real.exp (c * u) := by
    rw [div_le_iff₀ hS0]
    have h1 : Real.exp (c * u) * Real.exp (-(c * u)) = 1 := by rw [← Real.exp_add]; simp
    have h2 := mul_le_mul_of_nonneg_left hSlow (by positivity : (0 : ℝ) ≤ 2 * Real.exp (c * u))
    linarith
  have hfin : (|dLagReal D 0| + D.total * (16 * Real.exp (-(c * u)) ^ 2) *
      (1 + Real.exp (α * u))) / S ≤ 2 * |dLagReal D 0| * Real.exp (c * u) +
        32 * D.total * (Real.exp (-(c * u)) + Real.exp ((α - c) * u)) := by
    rw [div_eq_mul_one_div]
    refine (mul_le_mul_of_nonneg_left hinv hA0).trans (le_of_eq ?_)
    have e1 : Real.exp (-(c * u)) ^ 2 * Real.exp (c * u) = Real.exp (-(c * u)) := by
      rw [sq, mul_assoc, ← Real.exp_add]; simp
    have e2 : Real.exp (-(c * u)) ^ 2 * Real.exp (c * u) * Real.exp (α * u) =
        Real.exp ((α - c) * u) := by
      rw [e1, ← Real.exp_add]; ring_nf
    linear_combination (32 * D.total) * e1 + (32 * D.total) * e2
  linarith

theorem dWindow_bound_le_exp {α δ c a W W' K Φ0 C L : ℝ} (hδ0 : 0 < δ) (hc0 : 0 < c) (hL : 0 ≤ L)
    (hW : 0 ≤ W) (hW' : 0 ≤ W') (hK : 0 ≤ K) (hΦ0 : 0 ≤ Φ0) (hC : 0 ≤ C) (hca : c ≤ a)
    (hm : α - min c (δ / 4) ≤ a) :
    2 * Φ0 * Real.exp (c * L) + 32 * W * (Real.exp (-(c * L)) + Real.exp ((α - c) * L)) +
        K * (Real.exp (α * L) * (2 * Real.exp (1 / 2) * (3 / 2 * W' + 80 * (C + 2 + L)) *
          Real.exp (-(δ * L / 2)))) ≤
      (2 * Φ0 + 64 * W + K * (2 * Real.exp (1 / 2) * (3 / 2 * W' + 80 * (C + 2) + 80 * (4 / δ)))) *
        Real.exp (a * L) := by
  have hmc : min c (δ / 4) ≤ c := min_le_left _ _
  have hmd : min c (δ / 4) ≤ δ / 4 := min_le_right _ _
  have t1 : Real.exp (c * L) ≤ Real.exp (a * L) := Real.exp_le_exp.mpr (by nlinarith)
  have t2 : Real.exp (-(c * L)) ≤ Real.exp (a * L) := Real.exp_le_exp.mpr (by nlinarith)
  have t3 : Real.exp ((α - c) * L) ≤ Real.exp (a * L) := Real.exp_le_exp.mpr (by nlinarith)
  have t4 : Real.exp ((α - δ / 4) * L) ≤ Real.exp (a * L) := Real.exp_le_exp.mpr (by nlinarith)
  have e1 : Real.exp (α * L) * Real.exp (-(δ * L / 2)) =
      Real.exp ((α - δ / 4) * L) * Real.exp (-(δ * L / 4)) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  have h5 : Real.exp (δ * L / 4) * Real.exp (-(δ * L / 4)) = 1 := by rw [← Real.exp_add]; simp
  have h7 : Real.exp (-(δ * L / 4)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hlin : L ≤ 4 / δ * Real.exp (δ * L / 4) := by
    have := Real.add_one_le_exp (δ * L / 4)
    rw [div_mul_eq_mul_div, le_div_iff₀ hδ0]
    nlinarith
  have h8 : L * Real.exp (-(δ * L / 4)) ≤ 4 / δ := by
    have := mul_le_mul_of_nonneg_right hlin (Real.exp_pos (-(δ * L / 4))).le
    rwa [mul_assoc, h5, mul_one] at this
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = (3 / 2 * W' + 80 * (C + 2 + L)) * Real.exp (-(δ * L / 4)) :=
    ⟨_, rfl⟩
  have hQb : Q ≤ 3 / 2 * W' + 80 * (C + 2) + 80 * (4 / δ) := by
    have h9 : 0 ≤ 3 / 2 * W' + 80 * (C + 2) := by positivity
    have := mul_le_mul_of_nonneg_left h7 h9
    rw [hQ]
    nlinarith [Real.exp_pos (-(δ * L / 4))]
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  have e2 : Real.exp (α * L) * (2 * Real.exp (1 / 2) * (3 / 2 * W' + 80 * (C + 2 + L)) *
      Real.exp (-(δ * L / 2))) = 2 * Real.exp (1 / 2) * Q * Real.exp ((α - δ / 4) * L) := by
    rw [hQ]
    linear_combination (2 * Real.exp (1 / 2) * (3 / 2 * W' + 80 * (C + 2 + L))) * e1
  rw [e2]
  have he := Real.exp_pos (1 / 2 : ℝ)
  have k1 : 2 * Real.exp (1 / 2) * Q * Real.exp ((α - δ / 4) * L) ≤
      2 * Real.exp (1 / 2) * (3 / 2 * W' + 80 * (C + 2) + 80 * (4 / δ)) * Real.exp (a * L) := by
    gcongr
  have k1' := mul_le_mul_of_nonneg_left k1 hK
  have k2 := mul_le_mul_of_nonneg_left t1 (by positivity : (0 : ℝ) ≤ 2 * Φ0)
  have k3 := mul_le_mul_of_nonneg_left (add_le_add t2 t3) (by positivity : (0 : ℝ) ≤ 32 * W)
  nlinarith

/-- Positive windows at scale `u`: a set of primes with `log p ∈ [u, u + e^{−δu}]`, weight
`Σ p^{−σ} ≥ e^{−cu}`, on which the constant-vector product tests are positive. -/
def JasWeightedPositiveWindow (σ δ c u : ℝ) : Prop :=
  ∃ P : Finset Nat.Primes, JasWeightedConstPositiveOn D P σ ∧
    (∀ p ∈ P, u ≤ Real.log ((p : ℕ) : ℝ) ∧ Real.log ((p : ℕ) : ℝ) ≤ u + Real.exp (-(δ * u))) ∧
    Real.exp (-(c * u)) ≤ ∑ p ∈ P, Real.exp (-σ * Real.log ((p : ℕ) : ℝ))

/-- **Exponential growth of the lag function from positive windows.**  If positive windows exist
at all large scales, with `0 < δ ≤ 1` and `c > 0`, and `|Re ρ − ½| ≤ α`, then `|Φ(L)| ≤ M e^{aL}`
for all `L ≥ 0`, where `a = max(c, α − min(c, δ/4))`. -/
theorem exists_abs_dLagReal_le_exp_of_weightedWindows {σ α δ c : ℝ}
    (hα : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ α) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hc0 : 0 < c)
    (hW : ∀ᶠ u : ℝ in atTop, JasWeightedPositiveWindow D σ δ c u) :
    ∃ M : ℝ, ∀ L, 0 ≤ L →
      |dLagReal D L| ≤ M * Real.exp (max c (α - min c (δ / 4)) * L) := by
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = max c (α - min c (δ / 4)) := ⟨_, rfl⟩
  rw [← hadef]
  have hca : c ≤ a := hadef ▸ le_max_left _ _
  have hm : α - min c (δ / 4) ≤ a := hadef ▸ le_max_right _ _
  have ha0 : 0 ≤ a := by linarith
  have ev4 : ∀ᶠ u : ℝ in atTop, 4 * Real.exp (-(c * u)) ≤ 1 := by
    have ht : Tendsto (fun u : ℝ => Real.exp (-(c * u))) atTop (nhds 0) := by
      have := Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (show -c < 0 by linarith))
      refine this.congr fun u => ?_
      simp [Function.comp]
    filter_upwards [ht.eventually (ge_mem_nhds (show (0 : ℝ) < 1 / 4 by norm_num))] with u hu
    linarith
  obtain ⟨u₀, hu₀⟩ := eventually_atTop.mp (hW.and (ev4.and (eventually_ge_atTop (1 : ℝ))))
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 2 * |dLagReal D 0| + 64 * D.total +
      D.K * (2 * Real.exp (1 / 2) * (3 / 2 * lagWeightTotal + 80 * (|xiLineTwoLogDerivConstant| + 2) +
        80 * (4 / δ))) := ⟨_, rfl⟩
  have hW0 := D.total_nonneg
  refine ⟨max K (Real.exp (|u₀| / 2) * D.total), fun L hL => ?_⟩
  rcases le_or_gt u₀ L with hLu | hLu
  · obtain ⟨⟨P, hposP, hlogP, hMass⟩, hE4, hu1⟩ := hu₀ L hLu
    have hb := abs_dLagReal_le_of_window D hα hδ0 hu1 hE4 P hposP hlogP hMass
    have hcoh := diagCoherence_le hδ0 hδ1 hL
    have hb2 := hb.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hcoh (Real.exp_pos _).le) D.K_nonneg))
    have hw := dWindow_bound_le_exp (α := α) (W := D.total) (W' := lagWeightTotal) (K := D.K)
      (Φ0 := |dLagReal D 0|) (C := |xiLineTwoLogDerivConstant|) hδ0 hc0 hL hW0
      lagWeightTotal_nonneg D.K_nonneg (abs_nonneg _) (abs_nonneg _) hca hm
    rw [← hK] at hw
    exact (hb2.trans hw).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  · have h1 := abs_dLagReal_le D L
    rw [abs_of_nonneg hL] at h1
    have h2 : Real.exp (L / 2) ≤ Real.exp (|u₀| / 2) :=
      Real.exp_le_exp.mpr (by linarith [le_abs_self u₀])
    have h3 : 1 ≤ Real.exp (a * L) := Real.one_le_exp (mul_nonneg ha0 hL)
    have h4 : |dLagReal D L| ≤ Real.exp (|u₀| / 2) * D.total :=
      h1.trans (mul_le_mul_of_nonneg_right h2 hW0)
    have h5 : 0 ≤ max K (Real.exp (|u₀| / 2) * D.total) :=
      le_trans (by positivity) (le_max_right _ _)
    calc |dLagReal D L| ≤ max K (Real.exp (|u₀| / 2) * D.total) :=
          h4.trans (le_max_right _ _)
      _ ≤ max K (Real.exp (|u₀| / 2) * D.total) * Real.exp (a * L) :=
          le_mul_of_one_le_right h5 h3

/-- **Positive windows give the half-plane.**  If for every `0 < δ < 5/12` and every
`c₀ + δ < c < ½`, `c > 0`, positive windows exist at all large scales, then every zero satisfies
`|Re ρ − ½| ≤ max(0, c₀)`. -/
theorem abs_re_sub_half_le_of_weightedWindows {σ c₀ : ℝ}
    (hW : ∀ δ c : ℝ, 0 < δ → δ < 5 / 12 → 0 < c → c₀ + δ < c → c < 1 / 2 →
      ∀ᶠ u : ℝ in atTop, JasWeightedPositiveWindow D σ δ c u) (q : XiZeroCopy) :
    |(q.1 : ℂ).re - 1 / 2| ≤ max 0 c₀ := by
  haveI : Nonempty XiZeroCopy := ⟨q⟩
  obtain ⟨α, hαdef⟩ : ∃ α : ℝ, α = zeroReSup - 1 / 2 := ⟨_, rfl⟩
  have hXi : XiZeroHalfPlaneBound α := by
    intro ρ hρ
    obtain ⟨q', rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
    have := re_le_zeroReSup q'
    rw [hαdef]; linarith
  have hαall : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ α :=
    abs_re_sub_half_le_of_xiZeroHalfPlaneBound hXi
  have hαh : α ≤ 1 / 2 := by
    have := zeroReSup_le (fun q : XiZeroCopy => (xiZeroCopy_re_lt_one q).le)
    rw [hαdef]; linarith
  have key : ∀ δ c : ℝ, 0 < δ → δ < 5 / 12 → 0 < c → c₀ + δ < c → c < 1 / 2 → α ≤ c := by
    intro δ c hδ0 hδ hc0 hc hch
    obtain ⟨M, hM⟩ := exists_abs_dLagReal_le_exp_of_weightedWindows D hαall hδ0 (by linarith)
      hc0 (hW δ c hδ0 hδ hc0 hc hch)
    have hm0 : 0 < min c (δ / 4) := lt_min hc0 (by linarith)
    have ha0 : 0 ≤ max c (α - min c (δ / 4)) := le_trans hc0.le (le_max_left _ _)
    have ha : max c (α - min c (δ / 4)) < 1 / 2 := max_lt hch (by linarith)
    have hg : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ 1 / 2 + max c (α - min c (δ / 4)) := fun q =>
      re_le_half_add_of_dLagReal_le_exp D ha0 ha
        (fun L hL => (le_abs_self _).trans (hM L hL)) q
    have hsup := zeroReSup_le hg
    have hΘ : zeroReSup = α + 1 / 2 := by rw [hαdef]; ring
    have hle : α ≤ max c (α - min c (δ / 4)) := by linarith
    by_contra hlt
    push Not at hlt
    rcases le_total c (α - min c (δ / 4)) with h | h
    · rw [max_eq_right h] at hle; linarith
    · rw [max_eq_left h] at hle; linarith
  have hfin : α ≤ max 0 c₀ := by
    by_cases ht : 1 / 2 ≤ max 0 c₀
    · linarith
    · push Not at ht
      refine le_of_forall_pos_le_add fun ε hε => ?_
      rcases le_or_gt (1 / 2 - max 0 c₀) ε with hε' | hε'
      · linarith
      · have h1 := le_max_left 0 c₀
        have h2 := le_max_right 0 c₀
        have h3 := min_le_left (ε / 2) (1 / 4)
        have h4 := min_le_right (ε / 2) (1 / 4)
        exact key (min (ε / 2) (1 / 4)) (max 0 c₀ + ε) (lt_min (by linarith) (by norm_num))
          (by linarith) (by linarith) (by linarith) (by linarith)
  exact (hαall q).trans hfin

/-- Interval positivity supplies positive windows (the Huxley windows themselves). -/
theorem eventually_jasWeightedPositiveWindow_of_interval {X : ℕ} {σ : ℝ}
    (hpos : JasWeightedIntervalPositive D X σ) (hσ : 0 ≤ σ) {δ c : ℝ} (hδ0 : 0 < δ)
    (hδ : δ < 5 / 12) (hc0 : 0 < c) (hc : σ - 1 + δ < c) :
    ∀ᶠ u : ℝ in atTop, JasWeightedPositiveWindow D σ δ c u := by
  obtain ⟨X₀, -, hX₀⟩ := exists_theta_window_lower_seven_twelfths
    (α := (7 / 12 + (1 - δ)) / 2) (by linarith) (by linarith)
  filter_upwards [eventually_diagWindow_conditions X (σ := σ) (δ := δ) (c := c)
    (α' := (7 / 12 + (1 - δ)) / 2) (X₀ := X₀) (by linarith) (by linarith) hc0]
    with u hu
  obtain ⟨hE1, hE1', hE2, hE3, -, hu1⟩ := hu
  obtain ⟨P, hPdef, hlogP, hMass⟩ := exists_window (X := X) (c := c) hσ hδ0 (by linarith)
    (by linarith) hX₀ hu1 hE1 hE1' hE2 hE3
  refine ⟨P, ?_, hlogP, hMass⟩
  rw [hPdef]; exact hpos _ _ hE1' (Real.exp_pos _).le

/-- **Interval product positivity at level `σ` forces `|Re ρ − ½| ≤ max(0, σ − 1)`.** -/
theorem abs_re_sub_half_le_of_jasWeightedIntervalPositive {X : ℕ} {σ : ℝ}
    (hpos : JasWeightedIntervalPositive D X σ) (hσ : 0 ≤ σ) (q : XiZeroCopy) :
    |(q.1 : ℂ).re - 1 / 2| ≤ max 0 (σ - 1) :=
  abs_re_sub_half_le_of_weightedWindows D (fun _ _ hδ0 hδ hc0 hc _ =>
    eventually_jasWeightedPositiveWindow_of_interval D hpos hσ hδ0 hδ hc0 hc) q

theorem abs_re_sub_half_le_of_jasWeightedProductPositiveAbove {X : ℕ} {σ : ℝ}
    (hpos : JasWeightedProductPositiveAbove D X σ) (hσ : 0 ≤ σ) (q : XiZeroCopy) :
    |(q.1 : ℂ).re - 1 / 2| ≤ max 0 (σ - 1) :=
  abs_re_sub_half_le_of_jasWeightedIntervalPositive D hpos.intervalPositive hσ q


/-! ## The capstones -/

/-- **Dressed product positivity at a level `σ ≤ 1` implies RH.** -/
theorem riemannHypothesis_of_jasWeightedProductPositiveAbove {X : ℕ} {σ : ℝ}
    (hpos : JasWeightedProductPositiveAbove D X σ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    RiemannHypothesis := by
  refine riemannHypothesis_iff_xiZeroHalfPlaneBound_zero.mpr fun ρ hρ => ?_
  obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
  have := abs_re_sub_half_le_of_jasWeightedProductPositiveAbove D hpos hσ0 q
  rw [max_eq_left (by linarith)] at this
  linarith [le_abs_self ((q.1 : ℂ).re - 1 / 2)]

/-- **The dressed product abscissa law.**  Dressed positivity at a level `σ ≥ 1` gives
`sup Re ρ ≤ σ − ½`. -/
theorem xiZeroHalfPlaneBound_of_jasWeightedProductPositiveAbove {X : ℕ} {σ : ℝ}
    (hpos : JasWeightedProductPositiveAbove D X σ) (hσ : 1 ≤ σ) : XiZeroHalfPlaneBound (σ - 1) := by
  intro ρ hρ
  obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
  have := abs_re_sub_half_le_of_jasWeightedProductPositiveAbove D hpos (by linarith) q
  rw [max_eq_right (by linarith)] at this
  linarith [le_abs_self ((q.1 : ℂ).re - 1 / 2)]

/-- The dressing is positive at the zeros on the critical line. -/
def LagDressing.PositiveOnLine : Prop :=
  ∀ q : XiZeroCopy, (q.1 : ℂ).re = 1 / 2 → 0 < (D.g (q.1 : ℂ)).re

/-- On the critical line a dressing is real. -/
theorem LagDressing.im_g_eq_zero {s : ℂ} (hs : s.re = 1 / 2) : (D.g s).im = 0 := by
  have h1 : conj s = 1 - s := by
    apply Complex.ext
    · simp only [Complex.conj_re, Complex.sub_re, Complex.one_re]; linarith
    · simp
  have h := D.conj_eq s
  rw [h1, D.reflect_eq] at h
  have := congrArg Complex.im h
  rw [Complex.conj_im] at this
  linarith

/-- On the critical line the Bernoulli factor is `|1 + zA|² + |z|²(1 − |A|²)`. -/
theorem jasBernoulliFactor_of_re_eq_half {s : ℂ} (hs : s.re = 1 / 2) (σ : ℝ) (p : Nat.Primes)
    (z : ℂ) :
    jasBernoulliFactor (jasHoloA (s + (σ - 1 / 2 : ℝ)) p) (jasHoloB (s - (σ - 1 / 2 : ℝ)) p) z =
      ((‖1 + z * jasHoloA (s + (σ - 1 / 2 : ℝ)) p‖ ^ 2 +
        ‖z‖ ^ 2 * (1 - ‖jasHoloA (s + (σ - 1 / 2 : ℝ)) p‖ ^ 2) : ℝ) : ℂ) := by
  have hB : jasHoloB (s - (σ - 1 / 2 : ℝ)) p = conj (jasHoloA (s + (σ - 1 / 2 : ℝ)) p) := by
    unfold jasHoloA jasHoloB
    rw [← Complex.exp_conj]
    congr 1
    apply Complex.ext
    · simp only [Complex.neg_re, Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.add_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.neg_im,
        Complex.sub_im, Complex.add_im, Complex.one_im]
      rw [hs]; ring
    · simp only [Complex.neg_re, Complex.sub_re, Complex.one_re, Complex.add_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.conj_im, Complex.neg_im,
        Complex.mul_im, Complex.sub_im, Complex.add_im, Complex.one_im]
      ring
  rw [hB]
  unfold jasBernoulliFactor
  obtain ⟨A, hA⟩ : ∃ A : ℂ, A = jasHoloA (s + (σ - 1 / 2 : ℝ)) p := ⟨_, rfl⟩
  rw [← hA]
  push_cast
  rw [← Complex.mul_conj', ← Complex.mul_conj', ← Complex.mul_conj']
  simp only [map_add, map_one, map_mul]
  ring

theorem norm_jasHoloA_le_one {s : ℂ} (hs : s.re = 1 / 2) {σ : ℝ} (hσ : 0 ≤ σ) (p : Nat.Primes) :
    ‖jasHoloA (s + (σ - 1 / 2 : ℝ)) p‖ ≤ 1 := by
  rw [norm_jasHoloA, Real.exp_le_one_iff]
  have := log_prime_pos p
  simp only [Complex.add_re, Complex.ofReal_re, hs]
  nlinarith

/-- **RH gives dressed positivity at every level `σ ≥ 0`** for a dressing positive on the line. -/
theorem jasWeightedProductPositiveAbove_of_riemannHypothesis (hD : D.PositiveOnLine)
    (hRH : RiemannHypothesis) {σ : ℝ} (hσ : 0 ≤ σ) (X : ℕ) :
    JasWeightedProductPositiveAbove D X σ := by
  intro P _ z
  have hline : ∀ q : XiZeroCopy, (q.1 : ℂ).re = 1 / 2 := fun q => by
    have := abs_re_sub_half_le_of_xiZeroHalfPlaneBound
      (riemannHypothesis_iff_xiZeroHalfPlaneBound_zero.mp hRH) q
    have h0 := abs_nonneg ((q.1 : ℂ).re - 1 / 2)
    have : |(q.1 : ℂ).re - 1 / 2| = 0 := le_antisymm this h0
    linarith [abs_eq_zero.mp this]
  obtain ⟨t, htdef⟩ : ∃ t : XiZeroCopy → ℝ, t = fun q =>
      (∏ p ∈ P, (‖1 + z p * jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p‖ ^ 2 +
        ‖z p‖ ^ 2 * (1 - ‖jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p‖ ^ 2))) *
        ((D.g (q.1 : ℂ)).re / Complex.normSq (q.1 : ℂ)) := ⟨_, rfl⟩
  have hterm : ∀ q : XiZeroCopy,
      (∏ p ∈ P, jasBernoulliFactor (jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p)
        (jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) (z p)) * D.weight q = (t q : ℂ) := by
    intro q
    have hq := hline q
    rw [Finset.prod_congr rfl fun p _ => jasBernoulliFactor_of_re_eq_half hq σ p (z p)]
    have hg : D.g (q.1 : ℂ) = ((D.g (q.1 : ℂ)).re : ℂ) :=
      Complex.ext rfl (by rw [Complex.ofReal_im, D.im_g_eq_zero hq])
    have hden : (q.1 : ℂ) * (1 - (q.1 : ℂ)) = (Complex.normSq (q.1 : ℂ) : ℂ) := by
      have h1 : 1 - (q.1 : ℂ) = conj (q.1 : ℂ) := by
        apply Complex.ext
        · simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]; linarith
        · simp
      rw [h1, Complex.mul_conj]
    unfold LagDressing.weight
    rw [hg, hden, htdef]
    push_cast
    ring
  have hnn : ∀ q : XiZeroCopy, 0 ≤ t q := by
    intro q
    rw [htdef]
    have hq := hline q
    refine mul_nonneg (Finset.prod_nonneg fun p _ => ?_) (div_nonneg (hD q hq).le
      (Complex.normSq_nonneg _))
    have h1 := norm_jasHoloA_le_one hq hσ p
    have h2 : 0 ≤ 1 - ‖jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p‖ ^ 2 := by
      have := norm_nonneg (jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p)
      nlinarith
    positivity
  simp_rw [hterm]
  rw [← Complex.ofReal_tsum, Complex.ofReal_re]
  exact tsum_nonneg hnn

/-- **RH ⟺ dressed product positivity at level `1`**, for every dressing positive on the line. -/
theorem riemannHypothesis_iff_exists_jasWeightedProductPositiveAbove_one (hD : D.PositiveOnLine) :
    RiemannHypothesis ↔ ∃ X : ℕ, JasWeightedProductPositiveAbove D X 1 :=
  ⟨fun hRH => ⟨0, jasWeightedProductPositiveAbove_of_riemannHypothesis D hD hRH (by norm_num) 0⟩,
    fun ⟨_, h⟩ => riemannHypothesis_of_jasWeightedProductPositiveAbove D h (by norm_num) le_rfl⟩

end

end RHTower
