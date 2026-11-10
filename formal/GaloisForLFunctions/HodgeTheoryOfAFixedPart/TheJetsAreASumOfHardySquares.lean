import GaloisForLFunctions.HodgeTheoryOfAFixedPart.TheNormalFormOfThePairingOfTheDegreePoints

/-!
# The jets are a sum of Hardy squares

The jet of two degree points is the trace of `V_m F_n` on the archimedean fibre, a sum over the
weights `−2j`. In the normal form the term of the weight `−2j` is the kernel

  `k_j(m, n) = min(m, n)^{2j} / max(m, n)^{2j+1}`   (`jetLevel`).

* **The jets by weights** (`hasSum_jetLevel`): `½(1/|m − n| + 1/(m + n)) = Σ_{j ≥ 0} k_j(m, n)`
  for `m ≠ n`, and the first `J` weights leave the remainder `(min/max)^{2J}` times the jet
  (`jetKernel_sub_sum_jetLevel`).
* **Each weight is a Hardy square** (`sum_mul_mul_jetLevel_nonneg`): with the diagonal value
  `k_j(n, n) = 1/n` the kernel `k_j` is positive semidefinite. By Abel summation its form is a
  positive combination of the squares of the partial sums `Σ_{n ≤ t} c_n n^{2j}`
  (`le_sum_mul_mul_antitone_max`).
* **The diagonal that is left out** (`neg_le_sum_sum_jetLevel`): the off-diagonal form of the
  first `J` weights is at least `−J Σ c_n²/n`. Every weight leaves out one diagonal `Σ c_n²/n`;
  the counterterm of the comb replaces the sum of infinitely many of them.
* **Ordered approximations** (`combFormJets`, `combFormJets_le_combForm`,
  `combForm_sub_combFormJets`, `tendsto_combFormJets`): with the potential fixed and the Dirichlet
  form restricted to the first `J` weights, Weil's form on the comb increases with `J` to its
  value, and the error is half the Dirichlet form of the remainders `(min/max)^{2J}·jet`. On
  degree points up to `N` the remainder is at most `(1 − 1/N)^{2J}`
  (`combForm_sub_combFormJets_le`): at the scale `N` the pairing is resolved by a number of
  weights of the size `N`.
-/

open Finset Filter Topology

noncomputable section

namespace GaloisForLFunctions.HodgeTheoryOfAFixedPart

open AbsoluteGeometryOfSpecZ

/-! ### The jets by weights -/

/-- The jet of the weight `−2j` between two degree points: `min^{2j}/max^{2j+1}`. -/
def jetLevel (j m n : ℕ) : ℝ :=
  ((min m n : ℕ) : ℝ) ^ (2 * j) / ((max m n : ℕ) : ℝ) ^ (2 * j + 1)

theorem jetLevel_comm (j m n : ℕ) : jetLevel j m n = jetLevel j n m := by
  rw [jetLevel, jetLevel, min_comm, max_comm]

theorem jetLevel_nonneg (j m n : ℕ) : 0 ≤ jetLevel j m n := by
  unfold jetLevel
  positivity

theorem jetLevel_self (j : ℕ) {n : ℕ} (hn : 0 < n) : jetLevel j n n = 1 / (n : ℝ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [jetLevel, min_self, max_self, pow_succ]
  field_simp

/-- For `m < n` the jet of the weight `−2j` is `(1/n)·((m/n)²)^j`. -/
theorem jetLevel_of_lt (j : ℕ) {m n : ℕ} (hn : 0 < n) (hmn : m < n) :
    jetLevel j m n = 1 / (n : ℝ) * (((m : ℝ) / n) ^ 2) ^ j := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [jetLevel, min_eq_left hmn.le, max_eq_right hmn.le, ← pow_mul, div_pow, pow_succ]
  field_simp

/-- For `m < n` the jet is `(1/n)/(1 − (m/n)²)`. -/
theorem jetKernel_of_lt {m n : ℕ} (hmn : m < n) :
    jetKernel m n = 1 / (n : ℝ) * (1 - ((m : ℝ) / n) ^ 2)⁻¹ := by
  have hm' : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hlt : (m : ℝ) < n := by exact_mod_cast hmn
  have hn' : (0 : ℝ) < n := by linarith
  have h1 : (n : ℝ) - m ≠ 0 := by linarith
  have h2 : (n : ℝ) + m ≠ 0 := by linarith
  have h3 : (1 : ℝ) - ((m : ℝ) / n) ^ 2 ≠ 0 := by
    have : ((m : ℝ) / n) ^ 2 < 1 := by
      rw [div_pow, div_lt_one (by positivity)]
      nlinarith
    linarith
  rw [eq_mul_inv_iff_mul_eq₀ h3, jetKernel, abs_sub_comm, abs_of_pos (by linarith),
    add_comm (m : ℝ) n]
  field_simp
  ring

/-- **The jets by weights.** For distinct degree points the jet is the sum of its weights. -/
theorem hasSum_jetLevel {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n) :
    HasSum (fun j => jetLevel j m n) (jetKernel m n) := by
  wlog h : m < n generalizing m n
  · have hlt : n < m := lt_of_le_of_ne (not_lt.mp h) (Ne.symm hmn)
    have := this hn hm (Ne.symm hmn) hlt
    rw [jetKernel_comm]
    exact this.congr_fun fun j => jetLevel_comm j m n |>.symm ▸ rfl
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hr0 : (0 : ℝ) ≤ ((m : ℝ) / n) ^ 2 := sq_nonneg _
  have hr1 : ((m : ℝ) / n) ^ 2 < 1 := by
    have hlt : (m : ℝ) < n := by exact_mod_cast h
    rw [div_pow, div_lt_one (by positivity)]
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hgeo := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (1 / (n : ℝ))
  rw [jetKernel_of_lt h]
  exact hgeo.congr_fun fun j => (jetLevel_of_lt j hn h)

/-- **The remainder after `J` weights** is `(min/max)^{2J}` times the jet. -/
theorem jetKernel_sub_sum_jetLevel {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n) (J : ℕ) :
    jetKernel m n - ∑ j ∈ range J, jetLevel j m n =
      (((min m n : ℕ) : ℝ) / ((max m n : ℕ) : ℝ)) ^ (2 * J) * jetKernel m n := by
  wlog h : m < n generalizing m n
  · have hlt : n < m := lt_of_le_of_ne (not_lt.mp h) (Ne.symm hmn)
    have := this hn hm (Ne.symm hmn) hlt
    rw [jetKernel_comm m n, min_comm, max_comm, ← this]
    congr 1
    exact Finset.sum_congr rfl fun j _ => jetLevel_comm j m n
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hlt : (m : ℝ) < n := by exact_mod_cast h
  have hr1 : ((m : ℝ) / n) ^ 2 < 1 := by
    rw [div_pow, div_lt_one (by positivity)]
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hne : ((m : ℝ) / n) ^ 2 ≠ 1 := hr1.ne
  have hne' : (1 : ℝ) - ((m : ℝ) / n) ^ 2 ≠ 0 := by linarith
  have hne'' : ((m : ℝ) / n) ^ 2 - 1 ≠ 0 := by linarith
  have key : ∀ (A r : ℝ) (J : ℕ), 1 - r ≠ 0 → r - 1 ≠ 0 →
      A * (1 - r)⁻¹ - A * ((r ^ J - 1) / (r - 1)) = r ^ J * (A * (1 - r)⁻¹) := by
    intro A r J h1 h2
    field_simp
    ring
  rw [Finset.sum_congr rfl fun j _ => jetLevel_of_lt j hn h, ← Finset.mul_sum, geom_sum_eq hne,
    jetKernel_of_lt h, min_eq_left h.le, max_eq_right h.le, pow_mul]
  exact key _ _ _ hne' hne''

/-! ### Each weight is a Hardy square -/

/-- **Abel summation for a kernel of the maximum.** For `g` nonincreasing on the positive
integers, the form `Σ x_m x_n g(max(m, n))` on `[1, N]` is at least `g(N)(Σ x_n)²`. -/
theorem le_sum_mul_mul_antitone_max (g : ℕ → ℝ)
    (hg : ∀ t, 1 ≤ t → g (t + 1) ≤ g t) (x : ℕ → ℝ) :
    ∀ N : ℕ, g N * (∑ n ∈ Icc 1 N, x n) ^ 2 ≤
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, x m * x n * g (max m n) := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
    have hrow : ∀ m ∈ Icc 1 N, ∑ n ∈ Icc 1 (N + 1), x m * x n * g (max m n) =
        ∑ n ∈ Icc 1 N, x m * x n * g (max m n) + x m * x (N + 1) * g (N + 1) := by
      intro m hm
      have hmN := (Finset.mem_Icc.mp hm).2
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1), max_eq_right (by omega : m ≤ N + 1)]
    have hlast : ∑ n ∈ Icc 1 (N + 1), x (N + 1) * x n * g (max (N + 1) n) =
        (∑ n ∈ Icc 1 (N + 1), x n) * x (N + 1) * g (N + 1) := by
      rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun n hn => ?_
      rw [max_eq_left (Finset.mem_Icc.mp hn).2]
      ring
    have hsum : ∑ m ∈ Icc 1 N, x m * x (N + 1) * g (N + 1) =
        (∑ m ∈ Icc 1 N, x m) * x (N + 1) * g (N + 1) := by
      rw [Finset.sum_mul, Finset.sum_mul]
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1) (fun m => ∑ n ∈ Icc 1 (N + 1),
      x m * x n * g (max m n)), Finset.sum_congr rfl hrow, Finset.sum_add_distrib, hlast, hsum,
      Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
    have hmono : g (N + 1) * (∑ n ∈ Icc 1 N, x n) ^ 2 ≤ g N * (∑ n ∈ Icc 1 N, x n) ^ 2 := by
      rcases Nat.eq_zero_or_pos N with rfl | hN
      · simp
      · exact mul_le_mul_of_nonneg_right (hg N hN) (sq_nonneg _)
    linarith

/-- The jet of a weight as a kernel of the maximum. -/
theorem jetLevel_eq_max (j : ℕ) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    jetLevel j m n = (m : ℝ) ^ (2 * j) * (n : ℝ) ^ (2 * j) *
      (1 / ((max m n : ℕ) : ℝ) ^ (4 * j + 1)) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rcases le_total m n with h | h
  · rw [jetLevel, min_eq_left h, max_eq_right h]
    field_simp
    ring
  · rw [jetLevel, min_eq_right h, max_eq_left h]
    field_simp
    ring

/-- **Each weight is a Hardy square.** With the diagonal value `1/n` the jet of the weight `−2j`
is a positive semidefinite kernel on the degree points. -/
theorem sum_mul_mul_jetLevel_nonneg (j N : ℕ) (c : ℕ → ℝ) :
    0 ≤ ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, c m * c n * jetLevel j m n := by
  have h := le_sum_mul_mul_antitone_max (fun t => 1 / (t : ℝ) ^ (4 * j + 1))
    (fun t ht => by
      have ht' : (0 : ℝ) < t := by exact_mod_cast ht
      exact one_div_le_one_div_of_le (by positivity)
        (pow_le_pow_left₀ ht'.le (by push_cast; linarith) _))
    (fun n => c n * (n : ℝ) ^ (2 * j)) N
  have h0 : 0 ≤ 1 / (N : ℝ) ^ (4 * j + 1) * (∑ n ∈ Icc 1 N, c n * (n : ℝ) ^ (2 * j)) ^ 2 := by
    positivity
  refine (h0.trans h).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun n hn => ?_
  rw [jetLevel_eq_max j (by have := (Finset.mem_Icc.mp hm).1; omega)
    (by have := (Finset.mem_Icc.mp hn).1; omega)]
  ring

/-- **The diagonal that is left out.** The off-diagonal form of the first `J` weights of the jets
is at least `−J Σ c_n²/n`. -/
theorem neg_le_sum_sum_jetLevel (J N : ℕ) (c : ℕ → ℝ) :
    -(J : ℝ) * ∑ n ∈ Icc 1 N, c n ^ 2 / n ≤
      ∑ n ∈ Icc 1 N, ∑ m ∈ (Icc 1 N).erase n, c m * c n * ∑ j ∈ range J, jetLevel j m n := by
  have hlevel : ∀ j, ∑ n ∈ Icc 1 N, ∑ m ∈ (Icc 1 N).erase n, c m * c n * jetLevel j m n =
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, c m * c n * jetLevel j m n -
        ∑ n ∈ Icc 1 N, c n ^ 2 / n := by
    intro j
    rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [← Finset.add_sum_erase (Icc 1 N) _ hn,
      jetLevel_self j (by have := (Finset.mem_Icc.mp hn).1; omega)]
    ring
  have hswap : ∑ n ∈ Icc 1 N, ∑ m ∈ (Icc 1 N).erase n,
        c m * c n * ∑ j ∈ range J, jetLevel j m n =
      ∑ j ∈ range J, ∑ n ∈ Icc 1 N, ∑ m ∈ (Icc 1 N).erase n, c m * c n * jetLevel j m n := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun m _ => Finset.mul_sum _ _ _
  rw [hswap, Finset.sum_congr rfl fun j _ => hlevel j]
  have hge : ∀ j ∈ range J, -(∑ n ∈ Icc 1 N, c n ^ 2 / n) ≤
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, c m * c n * jetLevel j m n -
        ∑ n ∈ Icc 1 N, c n ^ 2 / n := fun j _ => by
    linarith [sum_mul_mul_jetLevel_nonneg j N c]
  calc -(J : ℝ) * ∑ n ∈ Icc 1 N, c n ^ 2 / n
      = ∑ _j ∈ range J, -(∑ n ∈ Icc 1 N, c n ^ 2 / n) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
    _ ≤ _ := Finset.sum_le_sum hge

/-! ### Ordered approximations -/

/-- Weil's form on the comb with the Dirichlet form of the jets restricted to the first `J`
weights, and the potential unchanged. -/
def combFormJets (J : ℕ) (S : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  2 * (degOne S c * degTwo S c) - ∑ n ∈ S, c n ^ 2 * combPotential S n +
    (∑ n ∈ S, ∑ m ∈ S.erase n,
      (c m - c n) ^ 2 * (∑ j ∈ range J, jetLevel j m n + contact m n)) / 2

/-- **The error of the first `J` weights** is half the Dirichlet form of the remainders
`(min/max)^{2J}·jet`. -/
theorem combForm_sub_combFormJets (J : ℕ) {S : Finset ℕ} (hS : ∀ n ∈ S, 0 < n) (c : ℕ → ℝ) :
    combForm S c - combFormJets J S c =
      (∑ n ∈ S, ∑ m ∈ S.erase n, (c m - c n) ^ 2 *
        ((((min m n : ℕ) : ℝ) / ((max m n : ℕ) : ℝ)) ^ (2 * J) * jetKernel m n)) / 2 := by
  have hD : combDirichlet S c - ∑ n ∈ S, ∑ m ∈ S.erase n,
        (c m - c n) ^ 2 * (∑ j ∈ range J, jetLevel j m n + contact m n) =
      ∑ n ∈ S, ∑ m ∈ S.erase n, (c m - c n) ^ 2 *
        ((((min m n : ℕ) : ℝ) / ((max m n : ℕ) : ℝ)) ^ (2 * J) * jetKernel m n) := by
    rw [combDirichlet, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [← jetKernel_sub_sum_jetLevel (hS m (Finset.mem_of_mem_erase hm)) (hS n hn)
      (Finset.ne_of_mem_erase hm) J, pairKernel]
    ring
  rw [combForm, combPairing_eq_potential_sub_dirichlet, combFormJets, ← hD]
  ring

/-- **The approximations are ordered below Weil's form.** -/
theorem combFormJets_le_combForm (J : ℕ) {S : Finset ℕ} (hS : ∀ n ∈ S, 0 < n) (c : ℕ → ℝ) :
    combFormJets J S c ≤ combForm S c := by
  have h := combForm_sub_combFormJets J hS c
  have h0 : 0 ≤ ∑ n ∈ S, ∑ m ∈ S.erase n, (c m - c n) ^ 2 *
      ((((min m n : ℕ) : ℝ) / ((max m n : ℕ) : ℝ)) ^ (2 * J) * jetKernel m n) :=
    Finset.sum_nonneg fun n _ => Finset.sum_nonneg fun m _ =>
      mul_nonneg (sq_nonneg _) (mul_nonneg (by positivity) (jetKernel_nonneg m n))
  linarith

/-- The approximations increase with the number of weights. -/
theorem combFormJets_mono {J J' : ℕ} (hJ : J ≤ J') (S : Finset ℕ) (c : ℕ → ℝ) :
    combFormJets J S c ≤ combFormJets J' S c := by
  unfold combFormJets
  have hle : ∑ n ∈ S, ∑ m ∈ S.erase n,
        (c m - c n) ^ 2 * (∑ j ∈ range J, jetLevel j m n + contact m n) ≤
      ∑ n ∈ S, ∑ m ∈ S.erase n,
        (c m - c n) ^ 2 * (∑ j ∈ range J', jetLevel j m n + contact m n) :=
    Finset.sum_le_sum fun n _ => Finset.sum_le_sum fun m _ =>
      mul_le_mul_of_nonneg_left (add_le_add
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hJ)
          fun j _ _ => jetLevel_nonneg j m n) le_rfl) (sq_nonneg _)
  linarith

/-- **At the scale `N` the remainder is at most `(1 − 1/N)^{2J}`.** For degree points up to `N`
the error of the first `J` weights is at most `(1 − 1/N)^{2J}` times half the Dirichlet form of
the jets. -/
theorem combForm_sub_combFormJets_le (J : ℕ) {N : ℕ} {S : Finset ℕ} (hS : S ⊆ Icc 1 N)
    (c : ℕ → ℝ) :
    combForm S c - combFormJets J S c ≤
      (1 - 1 / (N : ℝ)) ^ (2 * J) *
        ((∑ n ∈ S, ∑ m ∈ S.erase n, (c m - c n) ^ 2 * jetKernel m n) / 2) := by
  have hpos : ∀ n ∈ S, 0 < n := fun n hn => by
    have := (Finset.mem_Icc.mp (hS hn)).1
    omega
  rw [combForm_sub_combFormJets J hpos c, ← mul_div_assoc, Finset.mul_sum]
  refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun n hn => ?_) (by norm_num)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun m hm => ?_
  obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp (hS (Finset.mem_of_mem_erase hm))
  obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp (hS hn)
  have hne : m ≠ n := Finset.ne_of_mem_erase hm
  -- the ratio of two distinct degree points up to `N`
  have hmax0 : (0 : ℝ) < ((max m n : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < max m n)
  have hmaxN : ((max m n : ℕ) : ℝ) ≤ N := by exact_mod_cast (by omega : max m n ≤ N)
  have hmin : ((min m n : ℕ) : ℝ) + 1 ≤ ((max m n : ℕ) : ℝ) := by
    exact_mod_cast (by omega : min m n + 1 ≤ max m n)
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le hmax0 hmaxN
  have hratio : ((min m n : ℕ) : ℝ) / ((max m n : ℕ) : ℝ) ≤ 1 - 1 / (N : ℝ) := by
    rw [div_le_iff₀ hmax0]
    have h1 : 1 / (N : ℝ) * ((max m n : ℕ) : ℝ) ≤ 1 := by
      rw [one_div, inv_mul_le_iff₀ hN0]
      linarith
    nlinarith
  have hr0 : (0 : ℝ) ≤ ((min m n : ℕ) : ℝ) / ((max m n : ℕ) : ℝ) := by positivity
  have hpow := pow_le_pow_left₀ hr0 hratio (2 * J)
  have hk := jetKernel_nonneg m n
  have hsq := sq_nonneg (c m - c n)
  calc (c m - c n) ^ 2 *
        ((((min m n : ℕ) : ℝ) / ((max m n : ℕ) : ℝ)) ^ (2 * J) * jetKernel m n)
      ≤ (c m - c n) ^ 2 * ((1 - 1 / (N : ℝ)) ^ (2 * J) * jetKernel m n) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow hk) hsq
    _ = (1 - 1 / (N : ℝ)) ^ (2 * J) * ((c m - c n) ^ 2 * jetKernel m n) := by ring

/-- **The approximations converge to Weil's form.** -/
theorem tendsto_combFormJets {N : ℕ} {S : Finset ℕ} (hS : S ⊆ Icc 1 N) (c : ℕ → ℝ) :
    Tendsto (fun J : ℕ => combFormJets J S c) atTop (𝓝 (combForm S c)) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have hS0 : S = ∅ := by
      rw [← Finset.subset_empty]
      simpa using hS
    subst hS0
    simp [combFormJets, combForm, combPairing, degOne, degTwo]
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hpos : ∀ n ∈ S, 0 < n := fun n hn => by
    have := (Finset.mem_Icc.mp (hS hn)).1
    omega
  have hρ0 : (0 : ℝ) ≤ (1 - 1 / (N : ℝ)) ^ 2 := sq_nonneg _
  have hρ1 : (1 - 1 / (N : ℝ)) ^ 2 < 1 := by
    have h1 : (0 : ℝ) < 1 / (N : ℝ) := by positivity
    have h2 : 1 / (N : ℝ) ≤ 1 := by
      rw [div_le_one hN']
      exact_mod_cast hN
    nlinarith
  have hgeo := (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).mul_const
    ((∑ n ∈ S, ∑ m ∈ S.erase n, (c m - c n) ^ 2 * jetKernel m n) / 2)
  rw [zero_mul] at hgeo
  have hlow : Tendsto (fun J : ℕ => combForm S c -
      ((1 - 1 / (N : ℝ)) ^ 2) ^ J *
        ((∑ n ∈ S, ∑ m ∈ S.erase n, (c m - c n) ^ 2 * jetKernel m n) / 2)) atTop
      (𝓝 (combForm S c)) := by
    have := (tendsto_const_nhds (x := combForm S c)).sub hgeo
    rwa [sub_zero] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds (fun J => ?_)
    fun J => combFormJets_le_combForm J hpos c
  have h := combForm_sub_combFormJets_le J hS c
  rw [pow_mul] at h
  show combForm S c - ((1 - 1 / (N : ℝ)) ^ 2) ^ J *
      ((∑ n ∈ S, ∑ m ∈ S.erase n, (c m - c n) ^ 2 * jetKernel m n) / 2) ≤ combFormJets J S c
  linarith

end GaloisForLFunctions.HodgeTheoryOfAFixedPart
