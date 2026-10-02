import GaloisForLFunctions.RHTower.PMPowerDampedMobiusRamanujanKernelMass

/-!
# Signed prime balance at the natural Ramanujan cutoff

The centered prime factor of the actual transfer is not centered after a
natural cutoff. Its exact mean is a finite source difference minus the band
`Q/p < n ≤ Q`. The quadratic identity retains both terms for arbitrary
inputs. On prime-invariant inputs the cross form is negative semidefinite.
The literal Mobius-prefix input is not invariant; its physical energy remains
unbounded by these identities. No small-damping admission is claimed here.
-/

open scoped BigOperators
noncomputable section
namespace RHTower

/-- The literal centered prime factor in the signed Ramanujan transfer. -/
def pmRamanujanPrimeFeature (ε : ℝ) (p n : ℕ) : ℝ :=
  if p ∣ n then 1 else -1 / ((p : ℝ) ^ (1 + ε) - 1)

/-- The actual Ramanujan probability weight, restricted to a natural cutoff. -/
def pmRamanujanCutoffMean (ε : ℝ) (Q : ℕ) (H : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Finset.range (Q + 1), ‖pmPowerDampedRamanujanWeight ε n‖ * H n

/-- Nonmultiples of `p` in the literal boundary band `Q/p < n ≤ Q`. -/
def pmRamanujanPrimeBoundary (ε : ℝ) (p Q : ℕ) (H : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Finset.range (Q + 1) \ Finset.range (Q / p + 1),
    if p ∣ n then 0 else ‖pmPowerDampedRamanujanWeight ε n‖ * H n

/-- The complete prime difference, including its finite-cutoff boundary. -/
def pmRamanujanPrimeCutoffDifference (ε : ℝ) (p Q : ℕ) (H : ℕ → ℝ) : ℝ :=
  (∑ n ∈ Finset.range (Q / p + 1),
    if p ∣ n then 0 else
      ‖pmPowerDampedRamanujanWeight ε n‖ * (H (p * n) - H n)) -
    pmRamanujanPrimeBoundary ε p Q H

private theorem sum_range_dvd (H : ℕ → ℝ) {p : ℕ} (hp : 0 < p) (Q : ℕ) :
    (∑ n ∈ Finset.range (Q + 1), if p ∣ n then H n else 0) =
      ∑ n ∈ Finset.range (Q / p + 1), H (p * n) := by
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun n _ => p * n)
  · intro n hn
    simp only [Finset.mem_range, Nat.lt_succ_iff] at hn
    simp only [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
    exact ⟨by simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hp).mp hn,
      dvd_mul_right p n⟩
  · intro n hn m hm hnm
    exact Nat.eq_of_mul_eq_mul_left hp hnm
  · intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hn, hpn⟩
    refine ⟨n / p, ?_, ?_⟩
    · simp only [Finset.mem_range, Nat.lt_succ_iff] at hn ⊢
      exact Nat.div_le_div_right hn
    · exact Nat.mul_div_cancel' hpn
  · intro n hn
    rfl

private theorem cutoff_dvd_split {ε : ℝ} (hε : 0 < ε)
    {p : ℕ} (hp : p.Prime) (Q : ℕ) (H : ℕ → ℝ) :
    (∑ n ∈ Finset.range (Q + 1),
      if p ∣ n then ‖pmPowerDampedRamanujanWeight ε n‖ * H n else 0) =
    (∑ n ∈ Finset.range (Q / p + 1),
      if p ∣ n then 0 else ‖pmPowerDampedRamanujanWeight ε n‖ * H (p * n)) /
      ((p : ℝ) ^ (1 + ε) - 1) := by
  rw [sum_range_dvd _ hp.pos, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  rw [norm_pmPowerDampedRamanujanWeight_prime_mul hε hp]
  split_ifs <;> ring

private theorem prime_difference_eq (ε : ℝ) (p Q : ℕ) (H : ℕ → ℝ) :
    pmRamanujanPrimeCutoffDifference ε p Q H =
      (∑ n ∈ Finset.range (Q / p + 1),
        if p ∣ n then 0 else ‖pmPowerDampedRamanujanWeight ε n‖ * H (p * n)) -
      (∑ n ∈ Finset.range (Q + 1),
        if p ∣ n then 0 else ‖pmPowerDampedRamanujanWeight ε n‖ * H n) := by
  have hs : Finset.range (Q / p + 1) ⊆ Finset.range (Q + 1) :=
    Finset.range_mono (Nat.add_le_add_right (Nat.div_le_self Q p) 1)
  have hb := Finset.sum_sdiff_eq_sub hs
    (f := fun n => if p ∣ n then 0 else ‖pmPowerDampedRamanujanWeight ε n‖ * H n)
  have ht (n : ℕ) :
      (if p ∣ n then 0 else ‖pmPowerDampedRamanujanWeight ε n‖ * (H (p*n)-H n)) =
      (if p ∣ n then 0 else ‖pmPowerDampedRamanujanWeight ε n‖ * H (p*n)) -
      (if p ∣ n then 0 else ‖pmPowerDampedRamanujanWeight ε n‖ * H n) := by
    split_ifs <;> ring
  rw [pmRamanujanPrimeCutoffDifference, pmRamanujanPrimeBoundary,
    Finset.sum_congr rfl (fun n _ => ht n), Finset.sum_sub_distrib, hb]
  ring

/-- Exact signed cutoff balance; no invariance of the source input is assumed. -/
theorem pmRamanujanPrimeFeature_cutoff_mean {ε : ℝ} (hε : 0 < ε)
    {p : ℕ} (hp : p.Prime) (Q : ℕ) (H : ℕ → ℝ) :
    pmRamanujanCutoffMean ε Q (fun n => pmRamanujanPrimeFeature ε p n * H n) =
      pmRamanujanPrimeCutoffDifference ε p Q H / ((p : ℝ) ^ (1 + ε) - 1) := by
  rw [prime_difference_eq, pmRamanujanCutoffMean]
  have ht (n : ℕ) :
      ‖pmPowerDampedRamanujanWeight ε n‖ * (pmRamanujanPrimeFeature ε p n * H n) =
      (if p ∣ n then ‖pmPowerDampedRamanujanWeight ε n‖ * H n else 0) -
      (if p ∣ n then 0 else ‖pmPowerDampedRamanujanWeight ε n‖ * H n) /
        ((p : ℝ) ^ (1 + ε) - 1) := by
    simp only [pmRamanujanPrimeFeature]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun n _ => ht n), Finset.sum_sub_distrib,
    cutoff_dvd_split hε hp, ← Finset.sum_div]
  ring

theorem pmRamanujanPrimeFeature_eq_complement {ε : ℝ} (hε : 0 < ε)
    (n : ℕ) {p : ℕ} (hp : p.Prime) :
    pmRamanujanPrimeFeature ε p n = 1 - pmPowerDampedRamanujanPrimeCorrection ε n p := by
  exact (pmPowerDampedRamanujanPrimeCorrection_complement hε n hp).symm

private theorem prime_feature_sq {ε : ℝ} (hε : 0 < ε)
    {p : ℕ} (hp : p.Prime) (n : ℕ) :
    pmRamanujanPrimeFeature ε p n ^ 2 =
      1 / ((p : ℝ) ^ (1 + ε) - 1) +
      (((p : ℝ) ^ (1 + ε) - 1) - 1) / ((p : ℝ) ^ (1 + ε) - 1) *
        pmRamanujanPrimeFeature ε p n := by
  have hb : (p : ℝ) ^ (1 + ε) - 1 ≠ 0 := ne_of_gt
    (lt_trans (by norm_num) (pmPowerDampedRamanujan_prime_denominator_one_lt hε hp))
  simp only [pmRamanujanPrimeFeature]
  split_ifs <;> field_simp <;> ring

/-- The exact square identity includes the entire source change and cutoff band. -/
theorem pmRamanujanPrimeFeature_cutoff_quadratic {ε : ℝ} (hε : 0 < ε)
    {p : ℕ} (hp : p.Prime) (Q : ℕ) (f g : ℕ → ℝ) :
    let b := (p : ℝ) ^ (1 + ε) - 1
    pmRamanujanCutoffMean ε Q (fun n => (f n + pmRamanujanPrimeFeature ε p n * g n)^2) =
      pmRamanujanCutoffMean ε Q (fun n => f n ^ 2) +
      pmRamanujanCutoffMean ε Q (fun n => g n ^ 2) / b +
      2 * pmRamanujanPrimeCutoffDifference ε p Q (fun n => f n * g n) / b +
      (b - 1) * pmRamanujanPrimeCutoffDifference ε p Q (fun n => g n ^ 2) / b^2 := by
  dsimp only
  let b := (p : ℝ) ^ (1 + ε) - 1
  have he (n : ℕ) :
      ‖pmPowerDampedRamanujanWeight ε n‖ * (f n + pmRamanujanPrimeFeature ε p n * g n)^2 =
      ‖pmPowerDampedRamanujanWeight ε n‖ * f n^2 +
      (‖pmPowerDampedRamanujanWeight ε n‖ * g n^2) / b +
      2 * (‖pmPowerDampedRamanujanWeight ε n‖ *
        (pmRamanujanPrimeFeature ε p n * (f n * g n))) +
      ((b - 1) / b) * (‖pmPowerDampedRamanujanWeight ε n‖ *
        (pmRamanujanPrimeFeature ε p n * g n^2)) := by
    calc
      _ = ‖pmPowerDampedRamanujanWeight ε n‖ * f n^2 +
          ‖pmPowerDampedRamanujanWeight ε n‖ * pmRamanujanPrimeFeature ε p n^2 * g n^2 +
          2 * ‖pmPowerDampedRamanujanWeight ε n‖ * pmRamanujanPrimeFeature ε p n * f n * g n := by ring
      _ = _ := by rw [prime_feature_sq hε hp]; dsimp only [b]; ring
  have heSum := Finset.sum_congr (s₁ := Finset.range (Q+1)) rfl (fun n _ => he n)
  simp only [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum] at heSum
  change pmRamanujanCutoffMean ε Q _ =
    pmRamanujanCutoffMean ε Q (fun n => f n^2) +
    pmRamanujanCutoffMean ε Q (fun n => g n^2) / b +
    2 * pmRamanujanCutoffMean ε Q (fun n => pmRamanujanPrimeFeature ε p n * (f n*g n)) +
    ((b-1)/b) * pmRamanujanCutoffMean ε Q (fun n => pmRamanujanPrimeFeature ε p n * g n^2)
    at heSum
  rw [pmRamanujanPrimeFeature_cutoff_mean hε hp,
    pmRamanujanPrimeFeature_cutoff_mean hε hp] at heSum
  calc
    _ = _ := heSum
    _ = _ := by
      have hb : (p : ℝ) ^ (1 + ε) - 1 ≠ 0 := ne_of_gt
        (lt_trans (by norm_num) (pmPowerDampedRamanujan_prime_denominator_one_lt hε hp))
      dsimp only [b]
      field_simp [hb]

/-- Under prime invariance, the signed mean is precisely the negative boundary mass. -/
theorem pmRamanujanPrimeFeature_cutoff_invariant {ε : ℝ} (hε : 0 < ε)
    {p : ℕ} (hp : p.Prime) (Q : ℕ) (H : ℕ → ℝ)
    (hH : ∀ n, H (p*n) = H n) :
    pmRamanujanCutoffMean ε Q (fun n => pmRamanujanPrimeFeature ε p n * H n) =
      -pmRamanujanPrimeBoundary ε p Q H / ((p : ℝ) ^ (1 + ε) - 1) := by
  rw [pmRamanujanPrimeFeature_cutoff_mean hε hp, pmRamanujanPrimeCutoffDifference]
  simp only [hH, sub_self, mul_zero, ite_self, Finset.sum_const_zero, zero_sub]

/-- The whole truncated prime cross form is negative semidefinite on invariant inputs. -/
theorem pmRamanujanPrimeFeature_cutoff_invariant_square_nonpos {ε : ℝ} (hε : 0 < ε)
    {p : ℕ} (hp : p.Prime) (Q : ℕ) (H : ℕ → ℝ)
    (hH : ∀ n, H (p*n) = H n) :
    pmRamanujanCutoffMean ε Q (fun n => pmRamanujanPrimeFeature ε p n * H n^2) ≤ 0 := by
  rw [pmRamanujanPrimeFeature_cutoff_invariant hε hp Q (fun n => H n^2)
    (fun n => by rw [hH])]
  apply div_nonpos_of_nonpos_of_nonneg
  · apply neg_nonpos.mpr
    apply Finset.sum_nonneg
    intro n hn
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (norm_nonneg _) (sq_nonneg _)
  · exact (lt_trans (by norm_num) (pmPowerDampedRamanujan_prime_denominator_one_lt hε hp)).le

/-- Other prime factors are unchanged by multiplication by a new prime. -/
theorem pmRamanujanPrimeFeature_product_prime_mul (ε : ℝ)
    (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) {p : ℕ} (hp : p.Prime)
    (hpS : p ∉ S) (n : ℕ) :
    (∏ q ∈ S, pmRamanujanPrimeFeature ε q (p*n)) =
      ∏ q ∈ S, pmRamanujanPrimeFeature ε q n := by
  apply Finset.prod_congr rfl
  intro q hq
  have hqp : ¬q ∣ p := by
    intro hd
    rcases (Nat.dvd_prime hp).mp hd with h1 | heq
    · exact (hS q hq).ne_one h1
    · exact hpS (heq ▸ hq)
  simp only [pmRamanujanPrimeFeature, (hS q hq).dvd_mul, hqp, false_or]

/-- Actual signed prime factors have nonpositive one-prime cutoff covariance. -/
theorem pmRamanujanPrimeFeature_cutoff_product_cross_nonpos {ε : ℝ} (hε : 0 < ε)
    (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) {p : ℕ} (hp : p.Prime)
    (hpS : p ∉ S) (Q : ℕ) :
    pmRamanujanCutoffMean ε Q (fun n => pmRamanujanPrimeFeature ε p n *
      (∏ q ∈ S, pmRamanujanPrimeFeature ε q n)^2) ≤ 0 :=
  pmRamanujanPrimeFeature_cutoff_invariant_square_nonpos hε hp Q _
    (pmRamanujanPrimeFeature_product_prime_mul ε S hS hp hpS)

end RHTower
