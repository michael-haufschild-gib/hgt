import GaloisForLFunctions.ArithmeticOfSquareRootPrecision.TheDecidingInputTheorem
import GaloisForLFunctions.RHTower.MertensConstantAndCesaroIntegerLagBridge
import GaloisForLFunctions.RHTower.WeilPrimeDeficitSetRigidity

/-!
# A faithful input need not decide

The deciding-input theorem names four necessary properties of a statement `S` with `S ⇒ Count`: false for the Liouville twin, precision-faithful against `εn^{−η}`, of unbounded aperture, stabilizer
inside the square-root class `𝒬`.  This module shows that these properties are filters and not certificates, in two steps.

**The Mertens law** `Σ_{n ≤ N} a(n)/n = log N − γ + o(1)`, with the exact constant, is an unconditional theorem about `Λ` (`mertensLaw_vonMangoldt`).  It

* fails for the Liouville twin (`not_mertensLaw_liouvilleWeight`);
* is never shared by `a` and `a + εn^{−η}`, for every real `η` (`not_mertensLaw_and_add_smul_powerWeight`);
* is not determined by a finite window (`exists_extension_not_mertensLaw`);
* but its stabilizer contains `δ(n) = n^{−1/4} − κ 1_{n=1}`, outside `𝒬` (`mertensLaw_add_mertensInvisible`, `mertensInvisible_not_mem_sqrtClass`), so a weight satisfying it fails the count
  (`exists_mertensLaw_not_count`).

Precision-faithfulness only asks to pin one linear functional.  The stabilizer test is the one that does the work.

**Proximity** `a − Λ ∈ 𝒬` is true of `Λ` and passes all four tests (`proximity_passes_entry_criteria`).  It implies the count exactly if RH holds (`proximity_implies_count_iff`).  So a
true statement passing every necessary test can be as far from a proof as RH itself: the content of a deciding input is the proof of `S ⇒ Count`, and no list of necessary properties of `S` can certify it.
-/

noncomputable section

open Filter Topology Asymptotics Finset
open ArithmeticFunction (vonMangoldt cardFactors)

namespace GaloisForLFunctions.ArithmeticProduction

open ArithmeticOfSquareRootPrecision

/-- The harmonic sum `Σ_{n ≤ N} a(n)/n`. -/
def harmonicSum (a : ℕ → ℝ) (N : ℕ) : ℝ := ∑ n ∈ Icc 1 N, a n / n

/-- The Mertens law with its exact constant. -/
def MertensLaw (a : ℕ → ℝ) : Prop :=
  Tendsto (fun N : ℕ => harmonicSum a N - Real.log N) atTop (𝓝 (-Real.eulerMascheroniConstant))

theorem harmonicSum_add (a b : ℕ → ℝ) (N : ℕ) :
    harmonicSum (a + b) N = harmonicSum a N + harmonicSum b N := by
  unfold harmonicSum
  rw [← sum_add_distrib]
  refine sum_congr rfl fun n _ => ?_
  simp only [Pi.add_apply]
  ring

private theorem tendsto_natLog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- `B − k log N → −∞`. -/
private theorem tendsto_const_sub_log (B : ℝ) {k : ℝ} (hk : 0 < k) :
    Tendsto (fun N : ℕ => B + -k * Real.log N) atTop atBot :=
  tendsto_atBot_add_const_left atTop B (tendsto_natLog.const_mul_atTop_of_neg (by linarith))

/-- **The Mertens law for `Λ` is a theorem.** -/
theorem mertensLaw_vonMangoldt : MertensLaw vonMangoldtWeight := by
  obtain ⟨c, hc, C, -, hbound⟩ := RHTower.exists_global_mertensDeviation_exp_sqrt_log_bound
  have hsmall : Tendsto (fun N : ℕ => C * Real.exp (-c * √(Real.log N))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => √(Real.log N)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natLog
    have h2 : Tendsto (fun N : ℕ => Real.exp (-c * √(Real.log N))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (h1.const_mul_atTop_of_neg (by linarith))
    simpa using h2.const_mul C
  have h0 : Tendsto (fun N : ℕ => harmonicSum vonMangoldtWeight N - Real.log N +
      Real.eulerMascheroniConstant) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hsmall
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [Real.norm_eq_abs]
    exact hbound N hN
  have h1 := h0.sub_const Real.eulerMascheroniConstant
  simpa [MertensLaw] using h1

/-- **The Mertens law fails for the Liouville twin**: the two harmonic sums cancel on the primes, so a common law would make `2 log N` bounded. -/
theorem not_mertensLaw_liouvilleWeight : ¬ MertensLaw liouvilleWeight := by
  intro h
  have hs := RHTower.WeilPrimeDeficit.summable_nonprime_vonMangoldt_div
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = ∑' n : ℕ, if n.Prime then 0 else (vonMangoldt n : ℝ) / n := ⟨_, rfl⟩
  have hnn : ∀ n : ℕ, 0 ≤ if n.Prime then (0 : ℝ) else (vonMangoldt n : ℝ) / n := by
    intro n
    split_ifs
    · exact le_rfl
    · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg n)
  have hbound : ∀ N : ℕ, harmonicSum liouvilleWeight N + harmonicSum vonMangoldtWeight N ≤ 2 * B := by
    intro N
    have h1 : harmonicSum liouvilleWeight N + harmonicSum vonMangoldtWeight N =
        ∑ n ∈ Icc 1 N, (liouvilleWeight n + vonMangoldt n) / n := by
      unfold harmonicSum
      rw [← sum_add_distrib]
      refine sum_congr rfl fun n _ => ?_
      rw [add_div]
    rw [h1, hB]
    calc ∑ n ∈ Icc 1 N, (liouvilleWeight n + vonMangoldt n) / n
        ≤ ∑ n ∈ Icc 1 N, 2 * (if n.Prime then (0 : ℝ) else (vonMangoldt n : ℝ) / n) := by
          refine sum_le_sum fun n _ => ?_
          have h2 := (liouvilleWeight_add_vonMangoldt_le n).2
          have h3 := div_le_div_of_nonneg_right h2 (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
          refine h3.trans (le_of_eq ?_)
          split_ifs <;> ring
      _ = 2 * ∑ n ∈ Icc 1 N, (if n.Prime then (0 : ℝ) else (vonMangoldt n : ℝ) / n) := by
          rw [mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hs.sum_le_tsum _ fun n _ => hnn n) (by norm_num)
  have hadd := h.add mertensLaw_vonMangoldt
  have hbot : Tendsto (fun N : ℕ => (harmonicSum liouvilleWeight N - Real.log N) +
      (harmonicSum vonMangoldtWeight N - Real.log N)) atTop atBot := by
    refine tendsto_atBot_mono (fun N => ?_) (tendsto_const_sub_log (2 * B) (k := 2) two_pos)
    have := hbound N
    linarith
  exact not_tendsto_nhds_of_tendsto_atBot hbot _ hadd

/-- **The Mertens law is precision-faithful, at every power.** -/
theorem not_mertensLaw_and_add_smul_powerWeight (a : ℕ → ℝ) {ε : ℝ} (hε : ε ≠ 0) (η : ℝ) :
    ¬ (MertensLaw a ∧ MertensLaw (a + ε • powerWeight η)) := by
  rintro ⟨h1, h2⟩
  have hsub := h2.sub h1
  rw [sub_self] at hsub
  have hd : Tendsto (fun N : ℕ => harmonicSum (ε • powerWeight η) N) atTop (𝓝 0) := by
    refine hsub.congr fun N => ?_
    rw [harmonicSum_add]
    ring
  have hS : ∀ N : ℕ, 1 ≤ N → 1 ≤ ∑ n ∈ Icc 1 N, powerWeight η n / n := by
    intro N hN
    have hmem : 1 ∈ Icc 1 N := mem_Icc.mpr ⟨le_rfl, hN⟩
    have h3 := single_le_sum (f := fun n : ℕ => powerWeight η n / (n : ℝ))
      (fun n _ => div_nonneg (powerWeight_nonneg η n) (Nat.cast_nonneg n)) hmem
    simpa [powerWeight] using h3
  have hval : ∀ N : ℕ, harmonicSum (ε • powerWeight η) N = ε * ∑ n ∈ Icc 1 N, powerWeight η n / n := by
    intro N
    unfold harmonicSum
    rw [mul_sum]
    refine sum_congr rfl fun n _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hev := (hd.abs.eventually (gt_mem_nhds (by simpa using abs_pos.mpr hε : |(0 : ℝ)| < |ε|))).and
    (eventually_ge_atTop 1)
  obtain ⟨N, hN1, hN2⟩ := hev.exists
  rw [hval, abs_mul] at hN1
  have h3 := hS N hN2
  have h4 : |∑ n ∈ Icc 1 N, powerWeight η n / n| = ∑ n ∈ Icc 1 N, powerWeight η n / n :=
    abs_of_nonneg (by linarith)
  rw [h4] at hN1
  have h5 : |ε| * 1 ≤ |ε| * ∑ n ∈ Icc 1 N, powerWeight η n / n :=
    mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
  linarith

/-- **The Mertens law is not determined by a finite window.** -/
theorem exists_extension_not_mertensLaw (a : ℕ → ℝ) (X : ℕ) :
    ∃ b : ℕ → ℝ, (∀ n ≤ X, b n = a n) ∧ ¬ MertensLaw b := by
  refine ⟨fun n => if n ≤ X then a n else 0, fun n hn => by simp [hn], fun h => ?_⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = ∑ n ∈ Icc 1 X, |a n / n| := ⟨_, rfl⟩
  have hb : ∀ N : ℕ, harmonicSum (fun n => if n ≤ X then a n else 0) N ≤ B := by
    intro N
    unfold harmonicSum
    rw [hB]
    calc ∑ n ∈ Icc 1 N, (if n ≤ X then a n else 0) / (n : ℝ)
        = ∑ n ∈ (Icc 1 N).filter (· ≤ X), a n / n := by
          rw [sum_filter]
          refine sum_congr rfl fun n _ => ?_
          by_cases h : n ≤ X <;> simp [h]
      _ ≤ ∑ n ∈ (Icc 1 N).filter (· ≤ X), |a n / n| := sum_le_sum fun n _ => le_abs_self _
      _ ≤ _ := by
          refine sum_le_sum_of_subset_of_nonneg (fun n hn => ?_) fun _ _ _ => abs_nonneg _
          obtain ⟨h1, h2⟩ := mem_filter.mp hn
          exact mem_Icc.mpr ⟨(mem_Icc.mp h1).1, h2⟩
  have hbot : Tendsto (fun N : ℕ => harmonicSum (fun n => if n ≤ X then a n else 0) N - Real.log N)
      atTop atBot := by
    refine tendsto_atBot_mono (fun N => ?_) (tendsto_const_sub_log B (k := 1) one_pos)
    have := hb N
    linarith
  exact not_tendsto_nhds_of_tendsto_atBot hbot _ h

/-! ### The stabilizer of the Mertens law -/

/-- The harmonic mass of `n^{−1/4}`. -/
def mertensInvisibleConstant : ℝ := ∑' n : ℕ, powerWeight (1 / 4) n / n

/-- A perturbation with zero harmonic mass and square-root-visible partial sums. -/
def mertensInvisible (n : ℕ) : ℝ := powerWeight (1 / 4) n - if n = 1 then mertensInvisibleConstant else 0

theorem summable_powerWeight_div : Summable fun n : ℕ => powerWeight (1 / 4) n / n := by
  have h := Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 5 / 4)
  refine h.congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  unfold powerWeight
  rw [show (5 / 4 : ℝ) = 1 / 4 + 1 by norm_num, Real.rpow_add hpos, Real.rpow_one, mul_inv,
    Real.rpow_neg hpos.le]
  exact (div_eq_mul_inv _ _).symm

theorem tendsto_harmonicSum_powerWeight :
    Tendsto (fun N : ℕ => harmonicSum (powerWeight (1 / 4)) N) atTop (𝓝 mertensInvisibleConstant) := by
  have h := (tendsto_add_atTop_iff_nat 1).mpr summable_powerWeight_div.hasSum.tendsto_sum_nat
  refine h.congr fun N => ?_
  unfold harmonicSum
  refine (sum_subset (fun n hn => ?_) fun n hn hnot => ?_).symm
  · obtain ⟨-, h2⟩ := mem_Icc.mp hn
    exact mem_range.mpr (by omega)
  · have h0 : n = 0 := by
      by_contra hne
      exact hnot (mem_Icc.mpr ⟨Nat.pos_of_ne_zero hne, by have := mem_range.mp hn; omega⟩)
    simp [h0]

theorem harmonicSum_mertensInvisible {N : ℕ} (hN : 1 ≤ N) :
    harmonicSum mertensInvisible N = harmonicSum (powerWeight (1 / 4)) N - mertensInvisibleConstant := by
  unfold harmonicSum mertensInvisible
  simp only [sub_div]
  rw [sum_sub_distrib]
  congr 1
  rw [sum_eq_single 1]
  · simp
  · intro n _ hn
    simp [hn]
  · intro h
    exact absurd (mem_Icc.mpr ⟨le_rfl, hN⟩) h

/-- **The stabilizer of the Mertens law is large.** -/
theorem mertensLaw_add_mertensInvisible {a : ℕ → ℝ} (ha : MertensLaw a) :
    MertensLaw (a + mertensInvisible) := by
  have hd : Tendsto (fun N : ℕ => harmonicSum mertensInvisible N) atTop (𝓝 0) := by
    have h1 := tendsto_harmonicSum_powerWeight.sub_const mertensInvisibleConstant
    rw [sub_self] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact (harmonicSum_mertensInvisible hN).symm
  have h2 := ha.add hd
  rw [add_zero] at h2
  refine h2.congr fun N => ?_
  rw [harmonicSum_add]
  ring

/-- The perturbation is outside the square-root class. -/
theorem mertensInvisible_not_mem_sqrtClass : mertensInvisible ∉ sqrtClass := by
  intro h
  have h1 : (fun n => if n = 1 then mertensInvisibleConstant else 0 : ℕ → ℝ) ∈ sqrtClass :=
    mem_sqrtClass_of_eventually_zero (N := 1) fun n hn => by
      rw [if_neg (by omega)]
  have h2 := PrecisionClass.add_mem h h1
  have h3 : mertensInvisible + (fun n => if n = 1 then mertensInvisibleConstant else 0) =
      (1 : ℝ) • powerWeight (1 / 4) := by
    funext n
    simp [mertensInvisible]
  rw [h3] at h2
  exact smul_powerWeight_not_mem_sqrtClass one_ne_zero (by norm_num) (by norm_num) h2

/-- **A weight satisfying the Mertens law fails the count**, unconditionally. -/
theorem exists_mertensLaw_not_count : ∃ a : ℕ → ℝ, MertensLaw a ∧ ¬ Count a := by
  refine ⟨vonMangoldtWeight + mertensInvisible, mertensLaw_add_mertensInvisible mertensLaw_vonMangoldt,
    fun h => ?_⟩
  have h1 : ∀ n, 1 < n → (vonMangoldtWeight + mertensInvisible) n =
      (vonMangoldtWeight + (1 : ℝ) • powerWeight (1 / 4)) n := by
    intro n hn
    have hn1 : n ≠ 1 := by omega
    simp [mertensInvisible, hn1]
  exact not_count_vonMangoldt_add_smul_powerWeight one_ne_zero (by norm_num) (by norm_num)
    ((count_congr_of_eventually_eq h1).mp h)

/-! ### The tautological input -/

/-- Proximity to `Λ` at square-root precision. -/
def Proximity (a : ℕ → ℝ) : Prop := a - vonMangoldtWeight ∈ sqrtClass

theorem proximity_vonMangoldt : Proximity vonMangoldtWeight := by
  unfold Proximity
  rw [sub_self]
  exact PrecisionClass.zero_mem _

theorem not_proximity_liouvilleWeight : ¬ Proximity liouvilleWeight := by
  refine not_mem_precisionClass_of_lower_bound (g := fun x => x) (c := 1) sqrtScale_isLittleO_id
    one_pos ?_ ?_
  · have h1 := psi_sub_theta_isLittleO.def (c := 1 / 4) (by norm_num)
    filter_upwards [h1, eventually_abs_psi_sub_le (ε := 1 / 4) (by norm_num),
      eventually_gt_atTop (0 : ℝ)] with x hx1 hx2 hx0
    rw [Real.norm_of_nonneg hx0.le, Real.norm_eq_abs] at hx1
    rw [one_mul, Real.norm_of_nonneg hx0.le, Real.norm_eq_abs, partialSum_sub, partialSum_vonMangoldt]
    have h2 := (abs_le.mp hx1).2
    have h3 := (abs_le.mp hx2).1
    have h4 := (partialSum_liouvilleWeight_add_psi x).2
    have h5 : partialSum liouvilleWeight x - Chebyshev.psi x ≤ 0 := by linarith
    rw [abs_of_nonpos h5]
    linarith
  · exact (eventually_gt_atTop (0 : ℝ)).frequently.mono fun x hx => hx.ne'

/-- **Proximity passes every entry test**, and is true of `Λ`. -/
theorem proximity_passes_entry_criteria :
    Proximity vonMangoldtWeight ∧ ¬ Proximity liouvilleWeight ∧
    (∀ (a : ℕ → ℝ) (ε η : ℝ), ε ≠ 0 → 0 ≤ η → η < 1 / 2 →
      ¬ (Proximity a ∧ Proximity (a + ε • powerWeight η))) ∧
    (∀ (a : ℕ → ℝ) (X : ℕ), ∃ b : ℕ → ℝ, (∀ n ≤ X, b n = a n) ∧ ¬ Proximity b) ∧
    (∀ a δ : ℕ → ℝ, Proximity a → Proximity (a + δ) → δ ∈ sqrtClass) := by
  have hstab : ∀ a δ : ℕ → ℝ, Proximity a → Proximity (a + δ) → δ ∈ sqrtClass := by
    intro a δ h h'
    have h1 := PrecisionClass.sub_mem h' h
    have h2 : (a + δ - vonMangoldtWeight) - (a - vonMangoldtWeight) = δ := by abel
    rwa [h2] at h1
  refine ⟨proximity_vonMangoldt, not_proximity_liouvilleWeight, ?_, ?_, hstab⟩
  · rintro a ε η hε hη0 hη ⟨h, h'⟩
    exact smul_powerWeight_not_mem_sqrtClass hε hη0 hη (hstab a _ h h')
  · intro a X
    refine ⟨liouvilleTail a X, fun n hn => by simp [liouvilleTail, hn], fun h => ?_⟩
    have h1 : liouvilleWeight - liouvilleTail a X ∈ sqrtClass :=
      mem_sqrtClass_of_eventually_zero (N := X) fun n hn => by
        simp [liouvilleTail, not_le.mpr hn]
    have h2 := PrecisionClass.add_mem h1 h
    have h3 : (liouvilleWeight - liouvilleTail a X) + (liouvilleTail a X - vonMangoldtWeight) =
        liouvilleWeight - vonMangoldtWeight := by abel
    rw [h3] at h2
    exact not_proximity_liouvilleWeight h2

/-- **Whether proximity implies the count is RH.** -/
theorem proximity_implies_count_iff :
    (∀ a, Proximity a → Count a) ↔ RiemannHypothesis := by
  constructor
  · intro h
    exact count_vonMangoldt_iff.mp (h _ proximity_vonMangoldt)
  · intro hRH a ha
    have h1 := (count_add_iff_mem_sqrtClass (count_vonMangoldt_iff.mpr hRH) _).mpr ha
    simpa using h1

end GaloisForLFunctions.ArithmeticProduction
