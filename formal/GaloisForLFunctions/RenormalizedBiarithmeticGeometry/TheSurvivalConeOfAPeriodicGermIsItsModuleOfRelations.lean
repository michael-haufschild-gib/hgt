import GaloisForLFunctions.RenormalizedBiarithmeticGeometry.TheArchimedeanGermSurvivesOnItsPolarHyperplane

/-!
# The survival cone of a periodic germ is its module of relations

Both places of the explicit formula are instances of one construction. Take finitely many
*modes* `a_α : ℕ → ℝ`, periodic with a common period `q`, and *nodes* `x_α ≥ 0`. The periodic
Abel germ is the family

`Q_r(α, β) = Σ_{k ≥ 0} r^k a_α(k) a_β(k) / (k + 1 + x_α + x_β)`,  `0 ≤ r < 1`.

* **Positivity** (`periodicGerm_quad_nonneg`): each Abel level is a Cauchy form in the coefficients
  `C_α a_α(k)`, so every `Q_r` is positive semidefinite.
* **The counterterm is the Cesàro Gram** (`tendsto_twistedGerm_add_mean_log`). For a periodic `p`
  with mean `μ`, `Σ_k r^k p(k)/(k + w) + μ log(1 − r)` converges as `r → 1⁻`: the mean part is the
  lattice germ, the mean-zero part converges by Dirichlet's test and Abel's theorem. So the
  counterterm of the family is `M(α, β) = mean(a_α a_β)`.
* **Survival cone = relations** (`mem_survivalCone_cesaroGram_iff`). `C^T M C` is the mean square of
  `Σ_α C_α a_α`, which vanishes iff `Σ_α C_α a_α ≡ 0`.
* **The law** (`periodicGerm_survival`). The renormalized limit is nonnegative on every linear
  relation among the modes.

For the archimedean germ all modes are `1` and the relations are the polar hyperplane `Σ C_α = 0`;
for the torsion orbits the modes are Ramanujan sums, which carry no relations. A twin keeps
prime-side positivity only by adjoining modes that create relations — repeating a Ramanujan mode
`c_n` at several nodes makes `Σ_x C_{n,x} = 0` a relation.
-/

noncomputable section

open Filter Topology Finset

namespace GaloisForLFunctions.RenormalizedBiarithmeticGeometry

/-! ### Periodic sequences -/

/-- The mean of a sequence over the period `q`. -/
def periodMean (p : ℕ → ℝ) (q : ℕ) : ℝ := (∑ i ∈ range q, p i) / q

/-- Sums over a full period do not depend on the starting point. -/
theorem sum_range_shift_of_periodic {p : ℕ → ℝ} {q : ℕ} (hper : ∀ k, p (k + q) = p k) (j : ℕ) :
    ∑ i ∈ range q, p (j + i) = ∑ i ∈ range q, p i := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [← ih]
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · simp
    · have h1 := sum_range_succ (fun i => p (j + i)) q
      have h2 := sum_range_succ' (fun i => p (j + i)) q
      have h3 : ∑ i ∈ range q, p (j + 1 + i) = ∑ i ∈ range q, p (j + (i + 1)) :=
        sum_congr rfl fun i _ => by rw [show j + 1 + i = j + (i + 1) by ring]
      rw [h3]
      have hp : p (j + q) = p (j + 0) := by rw [add_zero, hper]
      linarith

/-- Partial sums of a periodic sequence reduce to partial sums of a remainder. -/
theorem sum_range_eq_sum_mod {p : ℕ → ℝ} {q : ℕ} (hq : 0 < q) (hper : ∀ k, p (k + q) = p k)
    (hzero : ∑ i ∈ range q, p i = 0) (n : ℕ) : ∑ i ∈ range n, p i = ∑ i ∈ range (n % q), p i := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n < q
    · rw [Nat.mod_eq_of_lt hn]
    · have hsplit : ∑ i ∈ range n, p i =
          ∑ i ∈ range (n - q), p i + ∑ i ∈ range q, p (n - q + i) := by
        rw [show n = (n - q) + q from (Nat.sub_add_cancel (by omega)).symm, sum_range_add]
        simp
      have hmod : (n - q) % q = n % q := by
        rw [← Nat.add_mod_right (n - q) q, Nat.sub_add_cancel (by omega : q ≤ n)]
      rw [hsplit, sum_range_shift_of_periodic hper, hzero, add_zero, ih (n - q) (by omega), hmod]

/-- Partial sums of a mean-zero periodic sequence are bounded. -/
theorem abs_sum_range_le_of_periodic {p : ℕ → ℝ} {q : ℕ} (hq : 0 < q) (hper : ∀ k, p (k + q) = p k)
    (hzero : ∑ i ∈ range q, p i = 0) (n : ℕ) : |∑ i ∈ range n, p i| ≤ ∑ i ∈ range q, |p i| := by
  rw [sum_range_eq_sum_mod hq hper hzero n]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  exact sum_le_sum_of_subset_of_nonneg (range_mono (Nat.mod_lt n hq).le)
    fun i _ _ => abs_nonneg _

/-- A periodic sequence is bounded by the sum of its absolute values over one period. -/
theorem abs_le_of_periodic {p : ℕ → ℝ} {q : ℕ} (hq : 0 < q) (hper : Function.Periodic p q)
    (k : ℕ) : |p k| ≤ ∑ i ∈ range q, |p i| := by
  rw [← hper.map_mod_nat k]
  exact single_le_sum (f := fun i => |p i|) (fun i _ => abs_nonneg _)
    (mem_range.mpr (Nat.mod_lt k hq))

/-! ### The counterterm of a periodic germ is its mean -/

/-- The Abel germ of `p` at weight `w`: `Σ_k r^k p(k)/(k + w)`. -/
def twistedGerm (p : ℕ → ℝ) (r w : ℝ) : ℝ := ∑' k : ℕ, r ^ k * p k / ((k : ℝ) + w)

theorem summable_twistedGerm {p : ℕ → ℝ} {B : ℝ} (hB : ∀ k, |p k| ≤ B) {r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r < 1) {w : ℝ} (hw : 0 < w) : Summable fun k : ℕ => r ^ k * p k / ((k : ℝ) + w) := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hr0 hr1).mul_right (B / w))
    fun k => ?_
  have hkw : 0 < (k : ℝ) + w := by positivity
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg (pow_nonneg hr0 k), abs_of_pos hkw]
  calc r ^ k * |p k| / ((k : ℝ) + w) ≤ r ^ k * B / w := by
        apply div_le_div₀ (mul_nonneg (pow_nonneg hr0 k) hB0)
          (mul_le_mul_of_nonneg_left (hB k) (pow_nonneg hr0 k)) hw
          (by linarith [k.cast_nonneg (α := ℝ)])
    _ = r ^ k * (B / w) := by ring

/-- **The counterterm of a periodic germ is its mean.** For a periodic `p` with mean `μ`,
`Σ_k r^k p(k)/(k + w) + μ log(1 − r)` converges as `r → 1⁻`. -/
theorem tendsto_twistedGerm_add_mean_log {p : ℕ → ℝ} {q : ℕ} (hq : 0 < q)
    (hper : Function.Periodic p q) {w : ℝ} (hw : 0 < w) :
    ∃ L : ℝ, Tendsto (fun r => twistedGerm p r w + periodMean p q * Real.log (1 - r))
      (𝓝[<] 1) (𝓝 L) := by
  set μ := periodMean p q
  set b : ℕ → ℝ := fun k => p k - μ
  have hbper : Function.Periodic b q := fun k => by simp only [b, hper k]
  have hbzero : ∑ i ∈ range q, b i = 0 := by
    simp only [b, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, μ, periodMean]
    field_simp
    ring
  -- Dirichlet's test: `Σ b(k)/(k + w)` converges.
  have hanti : Antitone fun k : ℕ => 1 / ((k : ℝ) + w) := fun i j hij => by
    have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  have hzero : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + w)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ w tendsto_natCast_atTop_atTop)
  have hcs := hanti.cauchySeq_series_mul_of_tendsto_zero_of_bounded hzero
    (b := ∑ i ∈ range q, |b i|) (z := b) fun n => by
      rw [Real.norm_eq_abs]; exact abs_sum_range_le_of_periodic hq hbper hbzero n
  obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hcs
  have hAbel := Real.tendsto_tsum_powerSeries_nhdsWithin_lt
    (f := fun k : ℕ => 1 / ((k : ℝ) + w) * b k) (l := l) (by simpa only [smul_eq_mul] using hl)
  refine ⟨μ * latticeGermLimit w + l, ?_⟩
  have hlat := (tendsto_latticeGerm_add_log hw).const_mul μ
  refine (hlat.add hAbel).congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
  have hbB : ∀ k, |b k| ≤ ∑ i ∈ range q, |b i| := abs_le_of_periodic hq hbper
  have hs1 := (hasSum_latticeGerm hr.1.le hr.2 hw).mul_left μ
  have hs2 := (summable_twistedGerm hbB hr.1.le hr.2 hw).hasSum
  have hsum := hs1.add hs2
  have heq : twistedGerm p r w = μ * latticeGerm r w +
      ∑' k : ℕ, r ^ k * b k / ((k : ℝ) + w) := by
    rw [twistedGerm, ← hsum.tsum_eq]
    refine tsum_congr fun k => ?_
    simp only [b]
    ring
  have hpow : ∑' k : ℕ, r ^ k * b k / ((k : ℝ) + w) =
      ∑' k : ℕ, 1 / ((k : ℝ) + w) * b k * r ^ k := tsum_congr fun k => by ring
  rw [heq, hpow]
  ring

/-! ### Periodic germ families -/

variable {n : ℕ}

/-- The periodic germ family with modes `a` and nodes `x`. -/
def periodicGerm (a : Fin n → ℕ → ℝ) (x : Fin n → ℝ) (r : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun α β => twistedGerm (fun k => a α k * a β k) r (1 + x α + x β)

/-- The Cesàro Gram of the modes: `M(α, β) = mean(a_α a_β)`. -/
def cesaroGram (a : Fin n → ℕ → ℝ) (q : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun α β => periodMean (fun k => a α k * a β k) q

/-- **Positivity of the periodic germ**: each Abel level is a Cauchy form. -/
theorem periodicGerm_quad_nonneg (a : Fin n → ℕ → ℝ) {q : ℕ} (hq : 0 < q)
    (hper : ∀ α, Function.Periodic (a α) q) {x : Fin n → ℝ} (hx : ∀ α, 0 ≤ x α) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (C : Fin n → ℝ) : 0 ≤ quad (periodicGerm a x r) C := by
  have hprod : ∀ α β, Function.Periodic (fun k => a α k * a β k) q := fun α β k => by
    simp only [hper α k, hper β k]
  have hB : ∀ α β k, |a α k * a β k| ≤ ∑ i ∈ range q, |a α i * a β i| :=
    fun α β => abs_le_of_periodic hq (hprod α β)
  have hw : ∀ α β, 0 < 1 + x α + x β := fun α β => by linarith [hx α, hx β]
  have h := hasSum_sum fun (α : Fin n) (_ : α ∈ univ) => hasSum_sum fun (β : Fin n) (_ : β ∈ univ) =>
    ((summable_twistedGerm (hB α β) hr0 hr1 (hw α β)).hasSum).mul_left (C α * C β)
  have hquad : quad (periodicGerm a x r) C = ∑ α, ∑ β, C α * C β * twistedGerm
      (fun k => a α k * a β k) r (1 + x α + x β) := by
    simp only [quad, periodicGerm, Matrix.of_apply]
    exact sum_congr rfl fun α _ => sum_congr rfl fun β _ => by ring
  rw [hquad]
  simp only [twistedGerm] at h ⊢
  refine h.nonneg fun k => ?_
  have hy : ∀ α, 0 < 1 / 2 + x α := fun α => by linarith [hx α]
  have hlev := cauchy_level_nonneg hy (fun α => C α * a α k) k
  have heq : ∑ α, ∑ β, C α * C β * (r ^ k * (a α k * a β k) / ((k : ℝ) + (1 + x α + x β))) =
      r ^ k * ∑ α, ∑ β, C α * a α k * (C β * a β k) * (1 / ((k : ℝ) + (1 / 2 + x α + (1 / 2 + x β)))) := by
    rw [mul_sum]
    refine sum_congr rfl fun α _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun β _ => ?_
    rw [show (1 / 2 + x α + (1 / 2 + x β) : ℝ) = 1 + x α + x β by ring]
    field_simp
  rw [heq]
  exact mul_nonneg (pow_nonneg hr0 k) hlev

/-- The Cesàro Gram form is the mean square of the combined mode. -/
theorem quad_cesaroGram (a : Fin n → ℕ → ℝ) (q : ℕ) (C : Fin n → ℝ) :
    quad (cesaroGram a q) C = (∑ k ∈ range q, (∑ α, C α * a α k) ^ 2) / q := by
  have hterm : ∀ α β, C α * cesaroGram a q α β * C β =
      ∑ k ∈ range q, C α * a α k * (C β * a β k) / q := by
    intro α β
    simp only [cesaroGram, Matrix.of_apply, periodMean, sum_div, mul_sum, sum_mul]
    exact sum_congr rfl fun k _ => by ring
  have hsq : ∀ k, (∑ α, C α * a α k) ^ 2 / q =
      ∑ α, ∑ β, C α * a α k * (C β * a β k) / q := by
    intro k
    rw [sq, sum_mul_sum, sum_div]
    exact sum_congr rfl fun α _ => by rw [sum_div]
  simp only [quad, hterm]
  rw [sum_div]
  simp only [hsq]
  calc ∑ α, ∑ β, ∑ k ∈ range q, C α * a α k * (C β * a β k) / q
      = ∑ α, ∑ k ∈ range q, ∑ β, C α * a α k * (C β * a β k) / q :=
        sum_congr rfl fun α _ => sum_comm
    _ = ∑ k ∈ range q, ∑ α, ∑ β, C α * a α k * (C β * a β k) / q := sum_comm

/-- **The survival cone of the Cesàro Gram is the module of relations among the modes.** -/
theorem mem_survivalCone_cesaroGram_iff (a : Fin n → ℕ → ℝ) {q : ℕ} (hq : 0 < q)
    (hper : ∀ α, Function.Periodic (a α) q) (C : Fin n → ℝ) :
    C ∈ survivalCone (cesaroGram a q) ↔ ∀ k, ∑ α, C α * a α k = 0 := by
  have hS : Function.Periodic (fun k => ∑ α, C α * a α k) q := fun k => by
    simp only [hper _ k]
  simp only [survivalCone, Set.mem_setOf_eq, quad_cesaroGram]
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [div_eq_zero_iff, or_iff_left hq', sum_eq_zero_iff_of_nonneg fun k _ => sq_nonneg _]
  constructor
  · intro h k
    rw [← hS.map_mod_nat k]
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (h _ (mem_range.mpr (Nat.mod_lt k hq)))
  · intro h k _
    rw [h k]
    ring

/-- **The survival law of periodic germs.** The renormalized limit of a periodic germ family is
nonnegative on every linear relation among its modes. -/
theorem periodicGerm_survival (a : Fin n → ℕ → ℝ) {q : ℕ} (hq : 0 < q)
    (hper : ∀ α, Function.Periodic (a α) q) {x : Fin n → ℝ} (hx : ∀ α, 0 ≤ x α) :
    ∃ A : Matrix (Fin n) (Fin n) ℝ,
      (∀ α β, Tendsto (fun r => periodicGerm a x r α β - (-Real.log (1 - r)) * cesaroGram a q α β)
        (𝓝[<] 1) (𝓝 (A α β))) ∧
      ∀ C : Fin n → ℝ, (∀ k, ∑ α, C α * a α k = 0) → 0 ≤ quad A C := by
  have hprod : ∀ α β, Function.Periodic (fun k => a α k * a β k) q := fun α β k => by
    simp only [hper α k, hper β k]
  have hlim : ∀ α β, ∃ L : ℝ, Tendsto (fun r => periodicGerm a x r α β -
      (-Real.log (1 - r)) * cesaroGram a q α β) (𝓝[<] 1) (𝓝 L) := by
    intro α β
    obtain ⟨L, hL⟩ := tendsto_twistedGerm_add_mean_log hq (hprod α β)
      (show 0 < 1 + x α + x β by linarith [hx α, hx β])
    exact ⟨L, hL.congr fun r => by simp only [periodicGerm, cesaroGram, Matrix.of_apply]; ring⟩
  choose A hA using hlim
  refine ⟨Matrix.of A, fun α β => hA α β, fun C hC => ?_⟩
  have hQ : ∀ᶠ r in 𝓝[<] (1 : ℝ), ∀ C, 0 ≤ quad (periodicGerm a x r) C := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr C
    exact periodicGerm_quad_nonneg a hq hper hx hr.1.le hr.2 C
  exact quad_nonneg_of_regularized hQ (fun α β => hA α β)
    ((mem_survivalCone_cesaroGram_iff a hq hper C).mpr hC)

end GaloisForLFunctions.RenormalizedBiarithmeticGeometry
