import GaloisForLFunctions.ArithmeticCriticalityTheory.GeneralGaugeGroundStateRepresentation
import GaloisForLFunctions.ArithmeticIncidencePositivity.PrimePowerIncidenceDominance

/-!
# The bump bridge: the prime part of `J_M` on bump profiles

For a gauge `M` with `|M(x)| ≤ C e^{−|x|}` the prime part of the signed jump energy is

`J_M^prime(u) = Σ_n Λ(n) n^{−1/2} ∫ M(x) M(x + log n) (u(x) − u(x + log n))² dx`.

On a bump profile `u_w = Σ_{p ∈ P} κ_p β((x − p)/w)` (`β` continuous, supported in `[−1, 1]`) it is of
order `w`, and (`tendsto_gaugePrimeJump_bumpProfile`)

`J_M^prime(u_w)/w → ∫β² · (Σ_p κ_p² M(p) 𝒢(M)(p) − Σ_{p,q} κ_p κ_q M(p) M(q) (a(q − p) + a(p − q)))`,

with the prime generator `𝒢(M)(y) = Σ_n Λ(n) n^{−1/2}(M(y + log n) + M(y − log n))` and the atom
`a(t) = Λ(n) n^{−1/2}` at a gap `t = log n` (`0` otherwise). Each shift splits into bump pairs, a pair
of distinct centres decouples once `w` is below half their distance, a coinciding pair concentrates to
`F(centre) ∫β²`, and `|z| + |z + log n| ≥ log n` dominates the shifts by `Λ(n) n^{−3/2}`.

On the even lattice `{± log a : a ∈ S}`, `S ⊆ {a ≥ 2}`, with an odd gauge the gaps are the ratio and
product atoms of the integers, and (`tendsto_gaugePrimeJump_latticeBumpProfile_netAtom`)

`J_M^prime(u_w)/w → ∫β² · (2 Σ_a c_a² M(log a) 𝒢(M)(log a) − 4 Σ_{a<b} c_a c_b M(log a) M(log b) netAtom(a, b)
  − 2 Σ_a c_a² M(log a)² netAtom(a, a))`,

where the last term is the crossing pair `(−log a, log a)` at the gap `log a²`. The pair statements of
the incidence classification are thus statements about the leading term of the zero form on lattice
profiles; the archimedean self-energy of a bump is of the larger order `w log(1/w)`.
-/

open MeasureTheory Set Filter Topology RHTower

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

open GaloisForLFunctions.ArithmeticCriticalityTheory

variable {β : ℝ → ℝ}

/-- Rescaling a pair of bumps: `∫ F(x) β((x−α)/w) β((x−α')/w) dx = w ∫ F(α + wy) β(y) β(y + (α−α')/w) dy`. -/
theorem integral_bump_pair_eq (F : ℝ → ℝ) (α α' : ℝ) {w : ℝ} (hw : 0 < w) :
    ∫ x, F x * β ((x - α) / w) * β ((x - α') / w) =
      w * ∫ y, F (α + w * y) * β y * β (y + (α - α') / w) := by
  have h1 : (fun x => F x * β ((x - α) / w) * β ((x - α') / w)) =
      fun x => (fun z => F (α + w * z) * β z * β (z + (α - α') / w)) ((x - α) / w) := by
    funext x
    simp only
    congr 2
    · congr 1; field_simp; ring
    · field_simp; ring
  rw [h1, integral_sub_right_eq_self (fun t => (fun z => F (α + w * z) * β z * β (z + (α - α') / w)) (t / w)) α,
    Measure.integral_comp_div (fun z => F (α + w * z) * β z * β (z + (α - α') / w)) w,
    abs_of_pos hw, smul_eq_mul]

/-- Distinct bump centres decouple once `w < |α − α'|/2`. -/
theorem integral_bump_pair_eq_zero (hβ : ∀ y, 1 < |y| → β y = 0) (F : ℝ → ℝ) {α α' w : ℝ}
    (hw : 0 < w) (hww : 2 * w < |α - α'|) :
    ∫ x, F x * β ((x - α) / w) * β ((x - α') / w) = 0 := by
  rw [integral_bump_pair_eq F α α' hw]
  have h0 : (fun y => F (α + w * y) * β y * β (y + (α - α') / w)) = fun _ => 0 := by
    funext y
    by_cases hy : 1 < |y|
    · rw [hβ y hy, mul_zero, zero_mul]
    · rw [not_lt] at hy
      have hbig : 1 < |y + (α - α') / w| := by
        have hq : 2 < |(α - α') / w| := by
          rw [abs_div, abs_of_pos hw, lt_div_iff₀ hw]; linarith
        have := abs_sub_abs_le_abs_sub ((α - α') / w) (-y)
        rw [abs_neg, sub_neg_eq_add, add_comm] at this
        linarith
      rw [hβ _ hbig, mul_zero]
  rw [h0, integral_zero, mul_zero]

/-- A single bump square concentrates: `(1/w) ∫ F(x) β((x−α)/w)² dx → F(α) ∫ β²`. -/
theorem tendsto_integral_bump_sq_div (hβc : Continuous β) (hβ : ∀ y, 1 < |y| → β y = 0)
    {F : ℝ → ℝ} (hF : Continuous F) (α : ℝ) :
    Tendsto (fun w => (∫ x, F x * β ((x - α) / w) * β ((x - α) / w)) / w) (𝓝[>] 0)
      (𝓝 (F α * ∫ y, β y ^ 2)) := by
  have heq : ∀ᶠ w in 𝓝[>] (0 : ℝ),
      (∫ x, F x * β ((x - α) / w) * β ((x - α) / w)) / w = ∫ y, F (α + w * y) * β y ^ 2 := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    have hw' : 0 < w := hw
    rw [integral_bump_pair_eq F α α hw', sub_self, zero_div, mul_div_cancel_left₀ _ hw'.ne']
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [add_zero]; ring
  refine Tendsto.congr' (EventuallyEq.symm heq) ?_
  -- dominated convergence on `[−1, 1]`
  have hsupp : ∀ y, 1 < |y| → β y ^ 2 = 0 := fun y hy => by rw [hβ y hy]; ring
  obtain ⟨K, hK⟩ : ∃ K, ∀ z ∈ Icc (α - 1) (α + 1), |F z| ≤ K :=
    (isCompact_Icc.exists_bound_of_continuousOn hF.continuousOn).imp fun K hK z hz => by
      simpa using hK z hz
  have hint : Integrable (fun y => K * β y ^ 2) := by
    refine (Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_)
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -1) (b := 1)) ?_
    intro y hy
    by_contra hmem
    rw [mem_Icc, not_and_or, not_le, not_le] at hmem
    have : 1 < |y| := by
      rcases hmem with h | h
      · exact lt_abs.mpr (Or.inr (by linarith))
      · exact lt_abs.mpr (Or.inl h)
    exact hy (by simp [hsupp y this])
  have hlim : Tendsto (fun w => ∫ y, F (α + w * y) * β y ^ 2) (𝓝[>] 0)
      (𝓝 (∫ y, F (α + 0 * y) * β y ^ 2)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun y => K * β y ^ 2) ?_ ?_ hint ?_
    · exact Eventually.of_forall fun w => (by fun_prop : Continuous fun y => F (α + w * y) * β y ^ 2).aestronglyMeasurable
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with w hw
      refine Eventually.of_forall fun y => ?_
      by_cases hy : 1 < |y|
      · rw [hsupp y hy]; simp
      · rw [not_lt] at hy
        have hz : α + w * y ∈ Icc (α - 1) (α + 1) := by
          have : |w * y| ≤ 1 := by
            rw [abs_mul, abs_of_pos hw.1]
            nlinarith [abs_nonneg y, hw.2]
          constructor <;> linarith [abs_le.mp this]
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (β y))]
        exact mul_le_mul_of_nonneg_right (hK _ hz) (sq_nonneg _)
    · refine Eventually.of_forall fun y => ?_
      exact ((hF.comp (continuous_const.add (continuous_id.mul continuous_const))).tendsto 0).mono_left
        nhdsWithin_le_nhds |>.mul_const _
  simp only [zero_mul, add_zero] at hlim
  rw [show F α * ∫ y, β y ^ 2 = ∫ y, F α * β y ^ 2 from (integral_const_mul _ _).symm]
  exact hlim


/-- `(1/w) ∫ F(x) β((x−α)/w) β((x−α')/w) dx → [α = α'] F(α) ∫ β²`. -/
theorem tendsto_integral_bump_pair_div (hβc : Continuous β) (hβ : ∀ y, 1 < |y| → β y = 0)
    {F : ℝ → ℝ} (hF : Continuous F) (α α' : ℝ) :
    Tendsto (fun w => (∫ x, F x * β ((x - α) / w) * β ((x - α') / w)) / w) (𝓝[>] 0)
      (𝓝 (if α = α' then F α * ∫ y, β y ^ 2 else 0)) := by
  split_ifs with h
  · subst h; exact tendsto_integral_bump_sq_div hβc hβ hF α
  · have hd : 0 < |α - α'| := abs_pos.mpr (sub_ne_zero.mpr h)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < |α - α'| / 2 by positivity)] with w hw
    rw [integral_bump_pair_eq_zero hβ F hw.1 (by linarith [hw.2]), zero_div]

/-- The bump profile `u_w(x) = Σ_{p ∈ P} κ_p β((x − p)/w)`. -/
def shiftedBumpProfile (β : ℝ → ℝ) (w : ℝ) (P : Finset ℝ) (κ : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ p ∈ P, κ p * β ((x - p) / w)

theorem continuous_shiftedBumpProfile (hβc : Continuous β) (w : ℝ) (P : Finset ℝ) (κ : ℝ → ℝ) :
    Continuous (shiftedBumpProfile β w P κ) := by
  unfold shiftedBumpProfile; fun_prop

/-- Expansion of one shift of the signed jump over pairs of bumps, with `F(x) = M(x)M(x+L)`. -/
theorem integral_signedShiftJump_bumpProfile (hβc : Continuous β) (hβ : ∀ y, 1 < |y| → β y = 0)
    {M : ℝ → ℝ} (hM : Continuous M) (P : Finset ℝ) (κ : ℝ → ℝ) (L : ℝ) {w : ℝ} (hw : 0 < w) :
    ∫ x, signedShiftJump M (shiftedBumpProfile β w P κ) L x =
      ∑ p ∈ P, ∑ q ∈ P, κ p * κ q *
        ((∫ x, M x * M (x + L) * β ((x - p) / w) * β ((x - q) / w)) -
          (∫ x, M x * M (x + L) * β ((x - p) / w) * β ((x - (q - L)) / w)) -
          (∫ x, M x * M (x + L) * β ((x - (p - L)) / w) * β ((x - q) / w)) +
          ∫ x, M x * M (x + L) * β ((x - (p - L)) / w) * β ((x - (q - L)) / w)) := by
  -- every bump product is continuous with compact support, hence integrable
  have hbump : ∀ α : ℝ, HasCompactSupport (fun x => β ((x - α) / w)) := fun α => by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := α - w) (b := α + w)) ?_
    intro x hx
    by_contra hmem
    have : 1 < |(x - α) / w| := by
      rw [abs_div, abs_of_pos hw, lt_div_iff₀ hw, one_mul]
      rw [mem_Icc, not_and_or, not_le, not_le] at hmem
      rcases hmem with h | h
      · exact lt_abs.mpr (Or.inr (by linarith))
      · exact lt_abs.mpr (Or.inl (by linarith))
    exact hx (hβ _ this)
  have hint : ∀ α α' : ℝ, Integrable (fun x => M x * M (x + L) * β ((x - α) / w) * β ((x - α') / w)) :=
    fun α α' => Continuous.integrable_of_hasCompactSupport (by fun_prop)
      ((hbump α').mul_left)
  have hpt : ∀ x, signedShiftJump M (shiftedBumpProfile β w P κ) L x =
      ∑ p ∈ P, ∑ q ∈ P, κ p * κ q *
        (M x * M (x + L) * β ((x - p) / w) * β ((x - q) / w) -
          M x * M (x + L) * β ((x - p) / w) * β ((x - (q - L)) / w) -
          M x * M (x + L) * β ((x - (p - L)) / w) * β ((x - q) / w) +
          M x * M (x + L) * β ((x - (p - L)) / w) * β ((x - (q - L)) / w)) := by
    intro x
    unfold signedShiftJump shiftedBumpProfile
    have hd : (∑ p ∈ P, κ p * β ((x - p) / w)) - ∑ p ∈ P, κ p * β ((x + L - p) / w) =
        ∑ p ∈ P, κ p * (β ((x - p) / w) - β ((x - (p - L)) / w)) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun p _ => by
        rw [show x + L - p = x - (p - L) by ring]; ring
    rw [hd, sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  have hcomb : ∀ p q : ℝ, Integrable (fun x => κ p * κ q *
      (M x * M (x + L) * β ((x - p) / w) * β ((x - q) / w) -
        M x * M (x + L) * β ((x - p) / w) * β ((x - (q - L)) / w) -
        M x * M (x + L) * β ((x - (p - L)) / w) * β ((x - q) / w) +
        M x * M (x + L) * β ((x - (p - L)) / w) * β ((x - (q - L)) / w))) := by
    intro p q
    refine Integrable.const_mul ?_ _
    exact (((hint p q).sub (hint p (q - L))).sub (hint (p - L) q)).add (hint (p - L) (q - L))
  simp_rw [hpt]
  rw [integral_finsetSum P (fun p _ => integrable_finsetSum P fun q _ => hcomb p q)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [integral_finsetSum P (fun q _ => hcomb p q)]
  refine Finset.sum_congr rfl fun q _ => ?_
  have h1 : Integrable (fun x => M x * M (x + L) * β ((x - p) / w) * β ((x - q) / w) -
      M x * M (x + L) * β ((x - p) / w) * β ((x - (q - L)) / w)) :=
    (hint p q).sub (hint p (q - L))
  have h2 : Integrable (fun x => M x * M (x + L) * β ((x - p) / w) * β ((x - q) / w) -
      M x * M (x + L) * β ((x - p) / w) * β ((x - (q - L)) / w) -
      M x * M (x + L) * β ((x - (p - L)) / w) * β ((x - q) / w)) := h1.sub (hint (p - L) q)
  rw [integral_const_mul, integral_add h2 (hint (p - L) (q - L)), integral_sub h1 (hint (p - L) q),
    integral_sub (hint p q) (hint p (q - L))]


/-- **One shift, limit.** `(1/w) ∫ M(x)M(x+L)(u_w(x) − u_w(x+L))² dx` tends to the bump-pair sum with
`F(x) = M(x)M(x+L)` read at coinciding centres. -/
theorem tendsto_shift_bumpProfile_div (hβc : Continuous β) (hβ : ∀ y, 1 < |y| → β y = 0)
    {M : ℝ → ℝ} (hM : Continuous M) (P : Finset ℝ) (κ : ℝ → ℝ) (L : ℝ) :
    Tendsto (fun w => (∫ x, signedShiftJump M (shiftedBumpProfile β w P κ) L x) / w) (𝓝[>] 0)
      (𝓝 (∑ p ∈ P, ∑ q ∈ P, κ p * κ q *
        ((if p = q then M p * M (p + L) * ∫ y, β y ^ 2 else 0) -
          (if p = q - L then M p * M (p + L) * ∫ y, β y ^ 2 else 0) -
          (if p - L = q then M (p - L) * M (p - L + L) * ∫ y, β y ^ 2 else 0) +
          (if p - L = q - L then M (p - L) * M (p - L + L) * ∫ y, β y ^ 2 else 0)))) := by
  have hF : Continuous fun x => M x * M (x + L) := by fun_prop
  have hJ := fun α α' => tendsto_integral_bump_pair_div hβc hβ hF α α'
  have heq : ∀ᶠ w in 𝓝[>] (0 : ℝ), (∫ x, signedShiftJump M (shiftedBumpProfile β w P κ) L x) / w =
      ∑ p ∈ P, ∑ q ∈ P, κ p * κ q *
        ((∫ x, M x * M (x + L) * β ((x - p) / w) * β ((x - q) / w)) / w -
          (∫ x, M x * M (x + L) * β ((x - p) / w) * β ((x - (q - L)) / w)) / w -
          (∫ x, M x * M (x + L) * β ((x - (p - L)) / w) * β ((x - q) / w)) / w +
          (∫ x, M x * M (x + L) * β ((x - (p - L)) / w) * β ((x - (q - L)) / w)) / w) := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    rw [integral_signedShiftJump_bumpProfile hβc hβ hM P κ L hw, Finset.sum_div]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  refine Tendsto.congr' (EventuallyEq.symm heq) ?_
  refine tendsto_finsetSum _ fun p _ => tendsto_finsetSum _ fun q _ => ?_
  exact (((hJ p q).sub (hJ p (q - L))).sub (hJ (p - L) q) |>.add (hJ (p - L) (q - L))).const_mul _

/-- A bump-pair integral, rescaled, is bounded by `sup |F| · sup |β| · ∫ |β|` over the unit
neighbourhood of the centre (`w ≤ 1`). -/
theorem abs_integral_bump_pair_div_le (hβc : Continuous β) (hβ : ∀ y, 1 < |y| → β y = 0)
    {F : ℝ → ℝ} {S Bβ : ℝ} (hS : ∀ z, |F z| ≤ S) (hB : ∀ y, |β y| ≤ Bβ)
    (α α' : ℝ) {w : ℝ} (hw : 0 < w) :
    |(∫ x, F x * β ((x - α) / w) * β ((x - α') / w)) / w| ≤ S * Bβ * ∫ y, |β y| := by
  rw [integral_bump_pair_eq F α α' hw, mul_div_cancel_left₀ _ hw.ne']
  have hβint : Integrable (fun y => |β y|) := by
    refine Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -1) (b := 1)) ?_
    intro y hy
    by_contra hmem
    rw [mem_Icc, not_and_or, not_le, not_le] at hmem
    have : 1 < |y| := by
      rcases hmem with h | h
      · exact lt_abs.mpr (Or.inr (by linarith))
      · exact lt_abs.mpr (Or.inl h)
    exact hy (by simp [hβ y this])
  calc |∫ y, F (α + w * y) * β y * β (y + (α - α') / w)|
      ≤ ∫ y, |F (α + w * y) * β y * β (y + (α - α') / w)| := abs_integral_le_integral_abs
    _ ≤ ∫ y, S * Bβ * |β y| := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
          (hβint.const_mul _) (Eventually.of_forall fun y => ?_)
        simp only
        rw [abs_mul, abs_mul]
        have h1 := hS (α + w * y)
        have h2 := hB (y + (α - α') / w)
        have h3 := abs_nonneg (β y)
        have hS0 : 0 ≤ S := (abs_nonneg _).trans (hS 0)
        calc |F (α + w * y)| * |β y| * |β (y + (α - α') / w)| ≤ S * |β y| * Bβ := by
              gcongr
          _ = S * Bβ * |β y| := by ring
    _ = S * Bβ * ∫ y, |β y| := integral_const_mul _ _

/-- Exponential decay of the gauge makes every shift conductance at most `C² e^{−|L|}`. -/
theorem abs_mul_shift_le {M : ℝ → ℝ} {C : ℝ} (hMC : ∀ x, |M x| ≤ C * Real.exp (-|x|)) (L z : ℝ) :
    |M z * M (z + L)| ≤ C ^ 2 * Real.exp (-|L|) := by
  have hC : 0 ≤ C := by
    have := (abs_nonneg _).trans (hMC 0)
    simpa using this
  rw [abs_mul]
  calc |M z| * |M (z + L)| ≤ (C * Real.exp (-|z|)) * (C * Real.exp (-|z + L|)) :=
        mul_le_mul (hMC z) (hMC _) (abs_nonneg _) (by positivity)
    _ = C ^ 2 * Real.exp (-(|z| + |z + L|)) := by
        rw [show -(|z| + |z + L|) = -|z| + -|z + L| by ring, Real.exp_add]; ring
    _ ≤ C ^ 2 * Real.exp (-|L|) := by
        gcongr
        have := abs_sub_abs_le_abs_sub (z + L) z
        have h2 := abs_add_le (z + L) (-z)
        rw [show z + L + -z = L by ring, abs_neg] at h2
        linarith

/-- `Σ_n Λ(n) n^{−1/2} e^{−log n}` converges. -/
theorem summable_vonMangoldtAtom_mul_exp_neg_log :
    Summable fun n : ℕ => vonMangoldtAtom n * Real.exp (-|Real.log n|) := by
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (vonMangoldtAtom_nonneg n) (Real.exp_pos _).le)
    (fun n => ?_) ((Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 5 / 4)).mul_left 4)
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n <;> simp [vonMangoldtAtom]
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hn1
    rw [abs_of_nonneg hlog0, Real.exp_neg, Real.exp_log hn0]
    unfold vonMangoldtAtom
    rw [if_pos hn]
    have hΛ : ArithmeticFunction.vonMangoldt n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
    have hlog : Real.log n ≤ (n : ℝ) ^ (1 / 4 : ℝ) / (1 / 4) :=
      Real.log_le_rpow_div hn0.le (by norm_num)
    have hs : Real.sqrt n = (n : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow n
    have key : (n : ℝ) ^ (1 / 4 : ℝ) / (1 / 4) / Real.sqrt n * (n : ℝ)⁻¹ = 4 * ((n : ℝ) ^ (5 / 4 : ℝ))⁻¹ := by
      rw [hs, show (5 / 4 : ℝ) = 1 / 2 + 1 - 1 / 4 by norm_num,
        Real.rpow_sub hn0, Real.rpow_add hn0, Real.rpow_one]
      field_simp
    calc ArithmeticFunction.vonMangoldt n / Real.sqrt n * (n : ℝ)⁻¹
        ≤ (n : ℝ) ^ (1 / 4 : ℝ) / (1 / 4) / Real.sqrt n * (n : ℝ)⁻¹ := by
          gcongr
          exact hΛ.trans hlog
      _ = 4 * ((n : ℝ) ^ (5 / 4 : ℝ))⁻¹ := key


/-- A bump of support `[−1, 1]` is bounded. -/
theorem exists_abs_le_of_bump (hβc : Continuous β) (hβ : ∀ y, 1 < |y| → β y = 0) :
    ∃ B, ∀ y, |β y| ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hβc.continuousOn
  refine ⟨max B 0, fun y => ?_⟩
  by_cases hy : 1 < |y|
  · rw [hβ y hy, abs_zero]; exact le_max_right _ _
  · rw [not_lt] at hy
    have h := hB y (mem_Icc.mpr (abs_le.mp hy))
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_max_left _ _)

/-- **One shift, uniform bound.** `|(1/w) ∫ M(x)M(x+L)(u_w(x) − u_w(x+L))²| ≤ K e^{−|L|}` for every
`w > 0`, with `K = 4C² Bβ (∫|β|) (Σ|κ_p|)²`. -/
theorem abs_shift_bumpProfile_div_le (hβc : Continuous β) (hβ : ∀ y, 1 < |y| → β y = 0)
    {M : ℝ → ℝ} (hM : Continuous M) {C : ℝ} (hMC : ∀ x, |M x| ≤ C * Real.exp (-|x|))
    {Bβ : ℝ} (hB : ∀ y, |β y| ≤ Bβ) (P : Finset ℝ) (κ : ℝ → ℝ) (L : ℝ) {w : ℝ} (hw : 0 < w) :
    |(∫ x, signedShiftJump M (shiftedBumpProfile β w P κ) L x) / w| ≤
      (∑ p ∈ P, |κ p|) ^ 2 * (4 * (C ^ 2 * Real.exp (-|L|) * Bβ * ∫ y, |β y|)) := by
  set S := C ^ 2 * Real.exp (-|L|)
  have hS : ∀ z, |M z * M (z + L)| ≤ S := abs_mul_shift_le hMC L
  have hb := fun α α' => abs_integral_bump_pair_div_le hβc hβ (F := fun x => M x * M (x + L)) hS hB α α' hw
  set T := S * Bβ * ∫ y, |β y| with hT
  rw [integral_signedShiftJump_bumpProfile hβc hβ hM P κ L hw, Finset.sum_div, sq, Finset.sum_mul_sum,
    Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => ?_)
  rw [Finset.sum_div, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun q _ => ?_)
  rw [mul_div_assoc, abs_mul, abs_mul]
  have e : ((∫ x, M x * M (x + L) * β ((x - p) / w) * β ((x - q) / w)) -
        (∫ x, M x * M (x + L) * β ((x - p) / w) * β ((x - (q - L)) / w)) -
        (∫ x, M x * M (x + L) * β ((x - (p - L)) / w) * β ((x - q) / w)) +
        ∫ x, M x * M (x + L) * β ((x - (p - L)) / w) * β ((x - (q - L)) / w)) / w =
      (∫ x, M x * M (x + L) * β ((x - p) / w) * β ((x - q) / w)) / w -
        (∫ x, M x * M (x + L) * β ((x - p) / w) * β ((x - (q - L)) / w)) / w -
        (∫ x, M x * M (x + L) * β ((x - (p - L)) / w) * β ((x - q) / w)) / w +
        (∫ x, M x * M (x + L) * β ((x - (p - L)) / w) * β ((x - (q - L)) / w)) / w := by ring
  rw [e]
  have h4 : |(∫ x, M x * M (x + L) * β ((x - p) / w) * β ((x - q) / w)) / w -
        (∫ x, M x * M (x + L) * β ((x - p) / w) * β ((x - (q - L)) / w)) / w -
        (∫ x, M x * M (x + L) * β ((x - (p - L)) / w) * β ((x - q) / w)) / w +
        (∫ x, M x * M (x + L) * β ((x - (p - L)) / w) * β ((x - (q - L)) / w)) / w| ≤ 4 * T := by
    have h1 := hb p q
    have h2 := hb p (q - L)
    have h3 := hb (p - L) q
    have h5 := hb (p - L) (q - L)
    have := abs_add_le ((∫ x, M x * M (x + L) * β ((x - p) / w) * β ((x - q) / w)) / w -
        (∫ x, M x * M (x + L) * β ((x - p) / w) * β ((x - (q - L)) / w)) / w -
        (∫ x, M x * M (x + L) * β ((x - (p - L)) / w) * β ((x - q) / w)) / w)
      ((∫ x, M x * M (x + L) * β ((x - (p - L)) / w) * β ((x - (q - L)) / w)) / w)
    have hsub1 := abs_sub ((∫ x, M x * M (x + L) * β ((x - p) / w) * β ((x - q) / w)) / w -
        (∫ x, M x * M (x + L) * β ((x - p) / w) * β ((x - (q - L)) / w)) / w)
      ((∫ x, M x * M (x + L) * β ((x - (p - L)) / w) * β ((x - q) / w)) / w)
    have hsub2 := abs_sub ((∫ x, M x * M (x + L) * β ((x - p) / w) * β ((x - q) / w)) / w)
      ((∫ x, M x * M (x + L) * β ((x - p) / w) * β ((x - (q - L)) / w)) / w)
    linarith
  calc |κ p| * |κ q| * |(∫ x, M x * M (x + L) * β ((x - p) / w) * β ((x - q) / w)) / w -
        (∫ x, M x * M (x + L) * β ((x - p) / w) * β ((x - (q - L)) / w)) / w -
        (∫ x, M x * M (x + L) * β ((x - (p - L)) / w) * β ((x - q) / w)) / w +
        (∫ x, M x * M (x + L) * β ((x - (p - L)) / w) * β ((x - (q - L)) / w)) / w|
      ≤ |κ p| * |κ q| * (4 * T) := mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = |κ p| * |κ q| * (4 * (C ^ 2 * Real.exp (-|L|) * Bβ * ∫ y, |β y|)) := by rw [hT]


/-- The prime part of the signed jump energy, `Σ_n Λ(n) n^{−1/2} ∫ M(x)M(x+log n)(u(x) − u(x+log n))²`. -/
def gaugePrimeJump (M u : ℝ → ℝ) : ℝ :=
  ∑' n : ℕ, vonMangoldtAtom n * ∫ x, signedShiftJump M u (Real.log n) x

/-- The limit of one shift: the bump-pair sum at coinciding centres (`F(x) = M(x)M(x+L)`). -/
def bumpShiftLimit (M : ℝ → ℝ) (P : Finset ℝ) (κ : ℝ → ℝ) (L B : ℝ) : ℝ :=
  ∑ p ∈ P, ∑ q ∈ P, κ p * κ q *
    ((if p = q then M p * M (p + L) * B else 0) -
      (if p = q - L then M p * M (p + L) * B else 0) -
      (if p - L = q then M (p - L) * M (p - L + L) * B else 0) +
      (if p - L = q - L then M (p - L) * M (p - L + L) * B else 0))

/-- **The bump bridge, analytic form.** For a gauge with `|M(x)| ≤ C e^{−|x|}` and a bump profile
`u_w = Σ_p κ_p β((· − p)/w)`, `(1/w)` times the prime part of `J_M(u_w)` converges as `w → 0⁺` to
`Σ_n Λ(n) n^{−1/2}` times the limit of the shift `log n`. -/
theorem tendsto_gaugePrimeJump_bumpProfile_div (hβc : Continuous β) (hβ : ∀ y, 1 < |y| → β y = 0)
    {M : ℝ → ℝ} (hM : Continuous M) {C : ℝ} (hMC : ∀ x, |M x| ≤ C * Real.exp (-|x|))
    (P : Finset ℝ) (κ : ℝ → ℝ) :
    Tendsto (fun w => gaugePrimeJump M (shiftedBumpProfile β w P κ) / w) (𝓝[>] 0)
      (𝓝 (∑' n : ℕ, vonMangoldtAtom n * bumpShiftLimit M P κ (Real.log n) (∫ y, β y ^ 2))) := by
  obtain ⟨Bβ, hB⟩ := exists_abs_le_of_bump hβc hβ
  set K := (∑ p ∈ P, |κ p|) ^ 2 * (4 * (C ^ 2 * Bβ * ∫ y, |β y|)) with hK
  have hK0 : 0 ≤ K := by
    have hC2 : 0 ≤ C ^ 2 := sq_nonneg C
    have hB0 : 0 ≤ Bβ := (abs_nonneg _).trans (hB 0)
    have hI : 0 ≤ ∫ y, |β y| := integral_nonneg fun _ => abs_nonneg _
    positivity
  have heq : (fun w => gaugePrimeJump M (shiftedBumpProfile β w P κ) / w) =
      fun w => ∑' n : ℕ, vonMangoldtAtom n * ((∫ x, signedShiftJump M (shiftedBumpProfile β w P κ)
        (Real.log n) x) / w) := by
    funext w
    unfold gaugePrimeJump
    rw [div_eq_mul_inv, ← tsum_mul_right]
    exact tsum_congr fun n => by ring
  rw [heq]
  refine tendsto_tsum_of_dominated_convergence
    (bound := fun n => K * (vonMangoldtAtom n * Real.exp (-|Real.log n|)))
    (summable_vonMangoldtAtom_mul_exp_neg_log.mul_left K) (fun n => ?_) ?_
  · exact (tendsto_shift_bumpProfile_div hβc hβ hM P κ (Real.log n)).const_mul _
  · filter_upwards [self_mem_nhdsWithin] with w hw n
    have hw' : 0 < w := hw
    have h := abs_shift_bumpProfile_div_le hβc hβ hM hMC hB P κ (Real.log n) hw'
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (vonMangoldtAtom_nonneg n)]
    calc vonMangoldtAtom n * |(∫ x, signedShiftJump M (shiftedBumpProfile β w P κ) (Real.log n) x) / w|
        ≤ vonMangoldtAtom n * ((∑ p ∈ P, |κ p|) ^ 2 *
            (4 * (C ^ 2 * Real.exp (-|Real.log n|) * Bβ * ∫ y, |β y|))) :=
          mul_le_mul_of_nonneg_left h (vonMangoldtAtom_nonneg n)
      _ = K * (vonMangoldtAtom n * Real.exp (-|Real.log n|)) := by rw [hK]; ring


/-! ### The limit in closed form -/

/-- The prime generator of the gauge, `𝒢(M)(y) = Σ_n Λ(n) n^{−1/2} (M(y + log n) + M(y − log n))`. -/
def primeGaugeGenerator (M : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∑' n : ℕ, vonMangoldtAtom n * (M (y + Real.log n) + M (y - Real.log n))

/-- The prime atom at the gap `t`: `Λ(n) n^{−1/2}` if `t = log n`, else `0`. -/
def primeAtomAtGap (t : ℝ) : ℝ := ∑' n : ℕ, if Real.log n = t then vonMangoldtAtom n else 0

theorem bumpShiftLimit_eq (M : ℝ → ℝ) (P : Finset ℝ) (κ : ℝ → ℝ) (L B : ℝ) :
    bumpShiftLimit M P κ L B =
      B * (∑ p ∈ P, κ p ^ 2 * (M p * (M (p + L) + M (p - L))) -
        ∑ p ∈ P, ∑ q ∈ P, κ p * κ q * (M p * M q) *
          ((if q - p = L then 1 else 0) + (if p - q = L then 1 else 0))) := by
  unfold bumpShiftLimit
  have hpt : ∀ p q : ℝ, κ p * κ q *
      ((if p = q then M p * M (p + L) * B else 0) -
        (if p = q - L then M p * M (p + L) * B else 0) -
        (if p - L = q then M (p - L) * M (p - L + L) * B else 0) +
        (if p - L = q - L then M (p - L) * M (p - L + L) * B else 0)) =
      (if p = q then κ p * κ q * (M p * (M (p + L) + M (p - L))) * B else 0) -
        κ p * κ q * (M p * M q) * ((if q - p = L then 1 else 0) + (if p - q = L then 1 else 0)) * B := by
    intro p q
    rw [show M (p - L + L) = M p by rw [sub_add_cancel]]
    by_cases h1 : p = q
    · subst h1
      by_cases hL0 : L = 0
      · subst hL0
        simp only [sub_zero, add_zero, sub_self, if_true]
        ring
      · have ha : ¬ (p = p - L) := fun h => hL0 (by linarith)
        have hb : ¬ (p - L = p) := fun h => hL0 (by linarith)
        have hc : ¬ (p - p = L) := fun h => hL0 (by linarith)
        simp only [if_true, if_neg ha, if_neg hb, if_neg hc]
        ring
    · have h4 : ¬ (p - L = q - L) := fun h => h1 (by linarith)
      rw [if_neg h1, if_neg h4, if_neg h1]
      by_cases h2 : q - p = L
      · have h2a : p = q - L := by linarith
        have h3a : ¬ (p - L = q) := fun h => h1 (by linarith)
        have h3 : ¬ (p - q = L) := fun h => h1 (by linarith)
        rw [if_pos h2a, if_neg h3a, if_pos h2, if_neg h3, show p + L = q by linarith]
        ring
      · have h2a : ¬ (p = q - L) := fun h => h2 (by linarith)
        by_cases h3 : p - q = L
        · have h3a : p - L = q := by linarith
          rw [if_neg h2a, if_pos h3a, if_neg h2, if_pos h3, h3a]
          ring
        · have h3a : ¬ (p - L = q) := fun h => h3 (by linarith)
          rw [if_neg h2a, if_neg h3a, if_neg h2, if_neg h3]
          ring
  simp_rw [hpt]
  rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq, if_pos hp, Finset.mul_sum]
  congr 1
  · ring
  · exact Finset.sum_congr rfl fun q _ => by ring


theorem summable_atom_indicator (t : ℝ) :
    Summable fun n : ℕ => if Real.log n = t then vonMangoldtAtom n else 0 := by
  refine summable_of_ne_finset_zero (s := Finset.range (⌈Real.exp t⌉₊ + 1)) fun n hn => ?_
  rw [Finset.mem_range, not_lt] at hn
  rw [if_neg]
  intro h
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have he : (n : ℝ) = Real.exp t := by rw [← h, Real.exp_log (by linarith)]
  have : (n : ℝ) ≤ ⌈Real.exp t⌉₊ := he ▸ Nat.le_ceil _
  have : n ≤ ⌈Real.exp t⌉₊ := by exact_mod_cast this
  omega

theorem summable_atom_mul_gauge_shift {M : ℝ → ℝ} {C : ℝ}
    (hMC : ∀ x, |M x| ≤ C * Real.exp (-|x|)) (p : ℝ) :
    Summable fun n : ℕ => vonMangoldtAtom n * (M (p + Real.log n) + M (p - Real.log n)) := by
  refine Summable.of_norm_bounded
    (summable_vonMangoldtAtom_mul_exp_neg_log.mul_left (2 * C * Real.exp |p|)) fun n => ?_
  have hC : 0 ≤ C := by have := (abs_nonneg _).trans (hMC 0); simpa using this
  set L := Real.log n
  have hexp : ∀ y : ℝ, |L| ≤ |y| + |p| → |M y| ≤ C * Real.exp |p| * Real.exp (-|L|) := by
    intro y hy
    calc |M y| ≤ C * Real.exp (-|y|) := hMC y
      _ ≤ C * Real.exp (|p| + -|L|) := by gcongr; linarith
      _ = C * Real.exp |p| * Real.exp (-|L|) := by rw [Real.exp_add]; ring
  have h1 := hexp (p + L) (by
    have := abs_sub_abs_le_abs_sub (p + L) p
    have h := abs_add_le (p + L) (-p)
    rw [show p + L + -p = L by ring, abs_neg] at h
    linarith)
  have h2 := hexp (p - L) (by
    have h := abs_add_le (p - L) (-p)
    rw [show p - L + -p = -L by ring, abs_neg, abs_neg] at h
    linarith)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (vonMangoldtAtom_nonneg n)]
  calc vonMangoldtAtom n * |M (p + L) + M (p - L)|
      ≤ vonMangoldtAtom n * (2 * (C * Real.exp |p| * Real.exp (-|L|))) := by
        refine mul_le_mul_of_nonneg_left ?_ (vonMangoldtAtom_nonneg n)
        have := abs_add_le (M (p + L)) (M (p - L))
        linarith
    _ = 2 * C * Real.exp |p| * (vonMangoldtAtom n * Real.exp (-|L|)) := by ring


/-- Summing the shift limits over the primes: the generator term minus the coinciding-pair atoms. -/
theorem tsum_atom_mul_bumpShiftLimit_eq {M : ℝ → ℝ} {C : ℝ}
    (hMC : ∀ x, |M x| ≤ C * Real.exp (-|x|)) (P : Finset ℝ) (κ : ℝ → ℝ) (B : ℝ) :
    ∑' n : ℕ, vonMangoldtAtom n * bumpShiftLimit M P κ (Real.log n) B =
      B * (∑ p ∈ P, κ p ^ 2 * (M p * primeGaugeGenerator M p) -
        ∑ p ∈ P, ∑ q ∈ P, κ p * κ q * (M p * M q) * (primeAtomAtGap (q - p) + primeAtomAtGap (p - q))) := by
  have hA : ∀ p : ℝ, Summable fun n : ℕ =>
      κ p ^ 2 * (M p * (vonMangoldtAtom n * (M (p + Real.log n) + M (p - Real.log n)))) :=
    fun p => ((summable_atom_mul_gauge_shift hMC p).mul_left (M p)).mul_left _
  have hD : ∀ p q : ℝ, Summable fun n : ℕ => κ p * κ q * (M p * M q) *
      ((if Real.log n = q - p then vonMangoldtAtom n else 0) +
        (if Real.log n = p - q then vonMangoldtAtom n else 0)) :=
    fun p q => ((summable_atom_indicator _).add (summable_atom_indicator _)).mul_left _
  have hpt : ∀ n : ℕ, vonMangoldtAtom n * bumpShiftLimit M P κ (Real.log n) B =
      B * (∑ p ∈ P, κ p ^ 2 * (M p * (vonMangoldtAtom n * (M (p + Real.log n) + M (p - Real.log n)))) -
        ∑ p ∈ P, ∑ q ∈ P, κ p * κ q * (M p * M q) *
          ((if Real.log n = q - p then vonMangoldtAtom n else 0) +
            (if Real.log n = p - q then vonMangoldtAtom n else 0))) := by
    intro n
    rw [bumpShiftLimit_eq, mul_left_comm, mul_sub, Finset.mul_sum, Finset.mul_sum]
    congr 2
    · exact Finset.sum_congr rfl fun p _ => by ring
    · refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      simp only [eq_comm (a := Real.log n)]
      split_ifs <;> ring
  rw [tsum_congr hpt, tsum_mul_left, Summable.tsum_sub (summable_sum fun p _ => hA p)
    (summable_sum fun p _ => summable_sum fun q _ => hD p q),
    Summable.tsum_finsetSum fun p _ => hA p,
    Summable.tsum_finsetSum fun p _ => summable_sum fun q _ => hD p q]
  congr 2
  · refine Finset.sum_congr rfl fun p _ => ?_
    rw [tsum_mul_left, tsum_mul_left]
    rfl
  · refine Finset.sum_congr rfl fun p _ => ?_
    rw [Summable.tsum_finsetSum fun q _ => hD p q]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [tsum_mul_left, Summable.tsum_add (summable_atom_indicator _) (summable_atom_indicator _)]
    rfl

/-- **The bump bridge.** For a gauge `M` with `|M(x)| ≤ C e^{−|x|}`, a bump `β` supported in
`[−1, 1]` and a profile `u_w = Σ_{p ∈ P} κ_p β((· − p)/w)`, the prime part of `J_M(u_w)`,
normalized by the width, converges as `w → 0⁺`:

`(1/w) Σ_n Λ(n) n^{−1/2} ∫ M(x)M(x + log n)(u_w(x) − u_w(x + log n))² dx
  → ∫β² · (Σ_p κ_p² M(p) 𝒢(M)(p) − Σ_{p,q} κ_p κ_q M(p) M(q) (a(q − p) + a(p − q)))`,

where `𝒢(M)(y) = Σ_n Λ(n) n^{−1/2}(M(y + log n) + M(y − log n))` is the prime generator of the gauge
and `a(t) = Λ(n) n^{−1/2}` if `t = log n`, else `0`, is the prime atom at the gap `t`. -/
theorem tendsto_gaugePrimeJump_bumpProfile (hβc : Continuous β) (hβ : ∀ y, 1 < |y| → β y = 0)
    {M : ℝ → ℝ} (hM : Continuous M) {C : ℝ} (hMC : ∀ x, |M x| ≤ C * Real.exp (-|x|))
    (P : Finset ℝ) (κ : ℝ → ℝ) :
    Tendsto (fun w => gaugePrimeJump M (shiftedBumpProfile β w P κ) / w) (𝓝[>] 0)
      (𝓝 ((∫ y, β y ^ 2) * (∑ p ∈ P, κ p ^ 2 * (M p * primeGaugeGenerator M p) -
        ∑ p ∈ P, ∑ q ∈ P, κ p * κ q * (M p * M q) * (primeAtomAtGap (q - p) + primeAtomAtGap (p - q))))) := by
  rw [← tsum_atom_mul_bumpShiftLimit_eq hMC]
  exact tendsto_gaugePrimeJump_bumpProfile_div hβc hβ hM hMC P κ


/-! ### The lattice `{± log a}` -/

theorem atomAt_eq_zero_of_neg {t : ℝ} (ht : t < 0) : primeAtomAtGap t = 0 := by
  unfold primeAtomAtGap
  refine (tsum_congr fun n => ?_).trans tsum_zero
  rw [if_neg]
  intro h
  have : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  linarith

/-- On the gap `log m` the atom is `Λ(m) m^{−1/2}`. -/
theorem atomAt_log_nat {m : ℕ} (hm : 1 ≤ m) : primeAtomAtGap (Real.log m) = vonMangoldtAtom m := by
  unfold primeAtomAtGap
  rw [tsum_eq_single m]
  · rw [if_pos rfl]
  · intro n hn
    split_ifs with h
    · rcases Nat.eq_zero_or_pos n with rfl | hn0
      · simp [vonMangoldtAtom]
      · exfalso
        have h1 : (0 : ℝ) < n := by exact_mod_cast hn0
        have h2 : (0 : ℝ) < m := by exact_mod_cast hm
        exact hn (by exact_mod_cast Real.log_injOn_pos (Set.mem_Ioi.mpr h1) (Set.mem_Ioi.mpr h2) h)
    · rfl


/-- On the gap `log b − log a` the atom is the ratio atom. -/
theorem atomAt_log_sub_log {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    primeAtomAtGap (Real.log b - Real.log a) = ratioAtom a b := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  unfold ratioAtom
  split_ifs with hab
  · obtain ⟨m, rfl⟩ := hab
    have hm : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with rfl | h
      · simp at hb
      · exact h
    rw [Nat.mul_div_cancel_left m (by omega), Nat.cast_mul,
      Real.log_mul haR.ne' (by exact_mod_cast (by omega : m ≠ 0)), add_sub_cancel_left,
      atomAt_log_nat hm]
  · unfold primeAtomAtGap
    refine (tsum_congr fun n => ?_).trans tsum_zero
    rw [if_neg]
    intro h
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp only [Nat.cast_zero, Real.log_zero] at h
      have : (b : ℝ) = a := Real.log_injOn_pos (Set.mem_Ioi.mpr hbR) (Set.mem_Ioi.mpr haR) (by linarith)
      exact hab ⟨1, by rw [mul_one]; exact_mod_cast this⟩
    · have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
      have e : Real.log ((n : ℝ) * a) = Real.log b := by rw [Real.log_mul hnR.ne' haR.ne', h]; ring
      have e2 : (n : ℝ) * a = b :=
        Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr hbR) e
      exact hab ⟨n, by rw [mul_comm]; exact_mod_cast e2.symm⟩

/-- On the gap `log a + log b` the atom is the product atom. -/
theorem atomAt_log_add_log {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    primeAtomAtGap (Real.log a + Real.log b) = productAtom a b := by
  rw [← Real.log_mul (by exact_mod_cast (by omega : a ≠ 0)) (by exact_mod_cast (by omega : b ≠ 0)),
    ← Nat.cast_mul, atomAt_log_nat (Nat.one_le_iff_ne_zero.mpr (by positivity)), productAtom]

theorem primeGaugeGenerator_neg {M : ℝ → ℝ} (hodd : ∀ x, M (-x) = -M x) (y : ℝ) :
    primeGaugeGenerator M (-y) = -primeGaugeGenerator M y := by
  unfold primeGaugeGenerator
  rw [← tsum_neg]
  refine tsum_congr fun n => ?_
  rw [show -y + Real.log n = -(y - Real.log n) by ring, show -y - Real.log n = -(y + Real.log n) by ring,
    hodd, hodd]
  ring

/-- The even lattice bump profile `u_w = Σ_{a ∈ S} c_a (β((x − log a)/w) + β((x + log a)/w))`. -/
def latticeBumpProfile (β : ℝ → ℝ) (w : ℝ) (S : Finset ℕ) (c : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ a ∈ S, c a * (β ((x - Real.log a) / w) + β ((x + Real.log a) / w))


/-- The lattice centres `{± log a : a ∈ S}`. -/
def latticeCentres (S : Finset ℕ) : Finset ℝ :=
  S.image (fun a : ℕ => Real.log a) ∪ S.image (fun a : ℕ => -Real.log a)

/-- The lattice coefficient `κ(± log a) = c_a`. -/
def latticeCoeff (c : ℕ → ℝ) (x : ℝ) : ℝ := c ⌊Real.exp |x|⌋₊

theorem latticeCoeff_log (c : ℕ → ℝ) {a : ℕ} (ha : 1 ≤ a) : latticeCoeff c (Real.log a) = c a := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  rw [latticeCoeff, abs_of_nonneg (Real.log_natCast_nonneg a), Real.exp_log haR, Nat.floor_natCast]

theorem latticeCoeff_neg_log (c : ℕ → ℝ) {a : ℕ} (ha : 1 ≤ a) :
    latticeCoeff c (-Real.log a) = c a := by
  have h := latticeCoeff_log c ha
  unfold latticeCoeff at h ⊢
  rwa [abs_neg]

/-- A sum over the lattice centres is a sum over `S` of both signs. -/
theorem sum_latticeCentres {S : Finset ℕ} (hS : ∀ a ∈ S, 2 ≤ a) (g : ℝ → ℝ) :
    ∑ p ∈ latticeCentres S, g p = ∑ a ∈ S, (g (Real.log a) + g (-Real.log a)) := by
  have hpos : ∀ a ∈ S, 0 < Real.log a := fun a ha =>
    Real.log_pos (by exact_mod_cast (by linarith [hS a ha] : 1 < a))
  have hinj : Set.InjOn (fun a : ℕ => Real.log a) S := by
    intro a ha b hb h
    have haR : (0 : ℝ) < a := by exact_mod_cast (by linarith [hS a ha] : 0 < a)
    have hbR : (0 : ℝ) < b := by exact_mod_cast (by linarith [hS b hb] : 0 < b)
    exact_mod_cast Real.log_injOn_pos (Set.mem_Ioi.mpr haR) (Set.mem_Ioi.mpr hbR) h
  have hinj' : Set.InjOn (fun a : ℕ => -Real.log a) S := fun a ha b hb h =>
    hinj ha hb (neg_injective h)
  have hdisj : Disjoint (S.image (fun a : ℕ => Real.log a)) (S.image (fun a : ℕ => -Real.log a)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp hx'
    linarith [hpos a ha, hpos b hb]
  rw [latticeCentres, Finset.sum_union hdisj, Finset.sum_image hinj, Finset.sum_image hinj',
    ← Finset.sum_add_distrib]

theorem latticeBumpProfile_eq {S : Finset ℕ} (hS : ∀ a ∈ S, 2 ≤ a) (c : ℕ → ℝ) (w : ℝ) :
    latticeBumpProfile β w S c = shiftedBumpProfile β w (latticeCentres S) (latticeCoeff c) := by
  funext x
  rw [shiftedBumpProfile, sum_latticeCentres hS]
  refine Finset.sum_congr rfl fun a ha => ?_
  have ha1 : 1 ≤ a := by linarith [hS a ha]
  rw [latticeCoeff_log c ha1, latticeCoeff_neg_log c ha1, sub_neg_eq_add]
  ring

/-- **The bump bridge on the lattice.** For an odd gauge with `|M(x)| ≤ C e^{−|x|}`, `S ⊆ {a ≥ 2}`
and the even lattice profile `u_w = Σ_{a ∈ S} c_a (β((x − log a)/w) + β((x + log a)/w))`,

`(1/w) · (prime part of J_M(u_w)) → ∫β² · (2 Σ_a c_a² M(log a) 𝒢(M)(log a)
  − 2 Σ_{a,b} c_a c_b M(log a) M(log b) (ratioAtom a b + ratioAtom b a − productAtom a b))`. -/
theorem tendsto_gaugePrimeJump_latticeBumpProfile (hβc : Continuous β) (hβ : ∀ y, 1 < |y| → β y = 0)
    {M : ℝ → ℝ} (hM : Continuous M) (hodd : ∀ x, M (-x) = -M x) {C : ℝ}
    (hMC : ∀ x, |M x| ≤ C * Real.exp (-|x|)) {S : Finset ℕ} (hS : ∀ a ∈ S, 2 ≤ a) (c : ℕ → ℝ) :
    Tendsto (fun w => gaugePrimeJump M (latticeBumpProfile β w S c) / w) (𝓝[>] 0)
      (𝓝 ((∫ y, β y ^ 2) * (2 * ∑ a ∈ S, c a ^ 2 * (M (Real.log a) * primeGaugeGenerator M (Real.log a)) -
        2 * ∑ a ∈ S, ∑ b ∈ S, c a * c b * (M (Real.log a) * M (Real.log b)) *
          (ratioAtom a b + ratioAtom b a - productAtom a b)))) := by
  simp_rw [latticeBumpProfile_eq hS]
  convert tendsto_gaugePrimeJump_bumpProfile hβc hβ hM hMC (latticeCentres S) (latticeCoeff c) using 3
  rw [sum_latticeCentres hS, sum_latticeCentres hS, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun a ha => ?_
    have ha1 : 1 ≤ a := by linarith [hS a ha]
    rw [latticeCoeff_log c ha1, latticeCoeff_neg_log c ha1, hodd, primeGaugeGenerator_neg hodd]
    ring
  · refine Finset.sum_congr rfl fun a ha => ?_
    have ha1 : 1 ≤ a := by linarith [hS a ha]
    rw [sum_latticeCentres hS, sum_latticeCentres hS, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b hb => ?_
    have hb1 : 1 ≤ b := by linarith [hS b hb]
    have hla : 0 < Real.log a := Real.log_pos (by exact_mod_cast (by linarith [hS a ha] : 1 < a))
    have hlb : 0 < Real.log b := Real.log_pos (by exact_mod_cast (by linarith [hS b hb] : 1 < b))
    rw [latticeCoeff_log c ha1, latticeCoeff_neg_log c ha1, latticeCoeff_log c hb1,
      latticeCoeff_neg_log c hb1, hodd, hodd,
      atomAt_log_sub_log ha1 hb1, atomAt_log_sub_log hb1 ha1,
      show -Real.log b - Real.log a = -(Real.log a + Real.log b) by ring,
      show Real.log a - -Real.log b = Real.log a + Real.log b by ring,
      show Real.log b - -Real.log a = Real.log a + Real.log b by ring,
      show -Real.log a - Real.log b = -(Real.log a + Real.log b) by ring,
      show -Real.log b - -Real.log a = Real.log a - Real.log b by ring,
      show -Real.log a - -Real.log b = Real.log b - Real.log a by ring,
      atomAt_log_sub_log ha1 hb1, atomAt_log_sub_log hb1 ha1, atomAt_log_add_log ha1 hb1,
      atomAt_eq_zero_of_neg (by linarith : -(Real.log a + Real.log b) < 0)]
    ring


theorem ratioAtom_eq_zero_of_not_lt {a b : ℕ} (hb : 1 ≤ b) (h : ¬ a < b) : ratioAtom a b = 0 := by
  unfold ratioAtom
  split_ifs with hab
  · rcases Nat.lt_or_ge b a with hlt | hge
    · exact absurd (Nat.le_of_dvd (by omega) hab) (by omega)
    · have : a = b := by omega
      subst this
      rw [Nat.div_self (by omega)]
      simp [vonMangoldtAtom]
  · rfl

/-- **Symmetric pair sums in net-atom form.** For a symmetric weight `X` on `S ⊆ {a ≥ 1}`,
`Σ_{a,b} X_{ab}(ratio(a,b) + ratio(b,a) − product(a,b)) = 2 Σ_{a<b} X_{ab} netAtom(a,b) + Σ_a X_{aa} netAtom(a,a)`. -/
theorem sum_sum_ratio_product_eq {S : Finset ℕ} (hS : ∀ a ∈ S, 1 ≤ a) (X : ℕ → ℕ → ℝ)
    (hX : ∀ a b, X a b = X b a) :
    ∑ a ∈ S, ∑ b ∈ S, X a b * (ratioAtom a b + ratioAtom b a - productAtom a b) =
      2 * ∑ a ∈ S, ∑ b ∈ S, (if a < b then X a b * netAtom a b else 0) +
        ∑ a ∈ S, X a a * netAtom a a := by
  -- the ratio atom lives above the diagonal
  have hr : ∀ a ∈ S, ∀ b ∈ S, X a b * ratioAtom a b = if a < b then X a b * ratioAtom a b else 0 :=
    fun a _ b hb => by
      split_ifs with h
      · rfl
      · rw [ratioAtom_eq_zero_of_not_lt (hS b hb) h, mul_zero]
  -- swapping the second ratio term
  have hswap : ∑ a ∈ S, ∑ b ∈ S, X a b * ratioAtom b a = ∑ a ∈ S, ∑ b ∈ S, X a b * ratioAtom a b := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [hX]
  -- splitting the product term into `a < b`, `a = b`, `b < a`
  have htri : ∀ a b : ℕ, X a b * productAtom a b =
      (if a < b then X a b * productAtom a b else 0) + (if a = b then X a b * productAtom a b else 0) +
        (if b < a then X a b * productAtom a b else 0) := fun a b => by
    rcases lt_trichotomy a b with h | h | h
    · rw [if_pos h, if_neg h.ne, if_neg (by omega)]; ring
    · rw [if_neg (by omega), if_pos h, if_neg (by omega)]; ring
    · rw [if_neg (by omega), if_neg h.ne', if_pos h]; ring
  have hlow : ∑ a ∈ S, ∑ b ∈ S, (if b < a then X a b * productAtom a b else 0) =
      ∑ a ∈ S, ∑ b ∈ S, (if a < b then X a b * productAtom a b else 0) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
      rw [hX, productAtom_comm]
  have hdiag : ∑ a ∈ S, ∑ b ∈ S, (if a = b then X a b * productAtom a b else 0) =
      ∑ a ∈ S, X a a * productAtom a a :=
    Finset.sum_congr rfl fun a ha => by rw [Finset.sum_ite_eq, if_pos ha]
  have hnet : ∀ a, X a a * netAtom a a = -(X a a * productAtom a a) := fun a => by
    rw [netAtom, ratioAtom]
    split_ifs
    · rcases Nat.eq_zero_or_pos a with rfl | ha
      · simp [vonMangoldtAtom]
      · rw [Nat.div_self ha]; simp [vonMangoldtAtom]
    · ring
  have hP : ∑ a ∈ S, ∑ b ∈ S, X a b * productAtom a b =
      2 * ∑ a ∈ S, ∑ b ∈ S, (if a < b then X a b * productAtom a b else 0) +
        ∑ a ∈ S, X a a * productAtom a a := by
    calc ∑ a ∈ S, ∑ b ∈ S, X a b * productAtom a b
        = ∑ a ∈ S, ∑ b ∈ S, ((if a < b then X a b * productAtom a b else 0) +
            (if a = b then X a b * productAtom a b else 0) +
            (if b < a then X a b * productAtom a b else 0)) :=
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => htri a b
      _ = _ := by
          simp only [Finset.sum_add_distrib]
          rw [hlow, hdiag]
          ring
  have hR : ∑ a ∈ S, ∑ b ∈ S, X a b * ratioAtom a b =
      ∑ a ∈ S, ∑ b ∈ S, (if a < b then X a b * ratioAtom a b else 0) :=
    Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => hr a ha b hb
  have hsplit : ∑ a ∈ S, ∑ b ∈ S, X a b * (ratioAtom a b + ratioAtom b a - productAtom a b) =
      ∑ a ∈ S, ∑ b ∈ S, X a b * ratioAtom a b + ∑ a ∈ S, ∑ b ∈ S, X a b * ratioAtom b a -
        ∑ a ∈ S, ∑ b ∈ S, X a b * productAtom a b := by
    simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have hcomb : ∀ a b : ℕ, (if a < b then X a b * netAtom a b else 0) =
      (if a < b then X a b * ratioAtom a b else 0) - (if a < b then X a b * productAtom a b else 0) :=
    fun a b => by split_ifs <;> simp [netAtom, mul_sub]
  rw [hsplit, hswap, hP, hR]
  simp_rw [hcomb, Finset.sum_sub_distrib, hnet, Finset.sum_neg_distrib]
  ring

/-- **The bump bridge on the lattice, net-atom form.** Under the hypotheses of
`tendsto_gaugePrimeJump_latticeBumpProfile`, the limit of `(1/w)` times the prime part of
`J_M(u_w)` is

`∫β² · (2 Σ_a c_a² M(log a) 𝒢(M)(log a) − 4 Σ_{a<b} c_a c_b M(log a) M(log b) netAtom(a,b)
  − 2 Σ_a c_a² M(log a)² netAtom(a,a))`. -/
theorem tendsto_gaugePrimeJump_latticeBumpProfile_netAtom (hβc : Continuous β)
    (hβ : ∀ y, 1 < |y| → β y = 0) {M : ℝ → ℝ} (hM : Continuous M) (hodd : ∀ x, M (-x) = -M x)
    {C : ℝ} (hMC : ∀ x, |M x| ≤ C * Real.exp (-|x|)) {S : Finset ℕ} (hS : ∀ a ∈ S, 2 ≤ a)
    (c : ℕ → ℝ) :
    Tendsto (fun w => gaugePrimeJump M (latticeBumpProfile β w S c) / w) (𝓝[>] 0)
      (𝓝 ((∫ y, β y ^ 2) * (2 * ∑ a ∈ S, c a ^ 2 * (M (Real.log a) * primeGaugeGenerator M (Real.log a)) -
        4 * ∑ a ∈ S, ∑ b ∈ S, (if a < b then
          c a * c b * (M (Real.log a) * M (Real.log b)) * netAtom a b else 0) -
        2 * ∑ a ∈ S, c a ^ 2 * M (Real.log a) ^ 2 * netAtom a a))) := by
  convert tendsto_gaugePrimeJump_latticeBumpProfile hβc hβ hM hodd hMC hS c using 3
  rw [sum_sum_ratio_product_eq (fun a ha => by linarith [hS a ha])
    (fun a b => c a * c b * (M (Real.log a) * M (Real.log b))) (fun a b => by ring)]
  have e : ∀ a : ℕ, c a * c a * (M (Real.log a) * M (Real.log a)) * netAtom a a =
      c a ^ 2 * M (Real.log a) ^ 2 * netAtom a a := fun a => by ring
  simp_rw [e]
  ring

end GaloisForLFunctions.ArithmeticIncidencePositivity
