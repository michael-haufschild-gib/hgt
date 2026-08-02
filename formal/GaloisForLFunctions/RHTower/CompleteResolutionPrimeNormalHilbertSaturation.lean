import GaloisForLFunctions.RHTower.PrimeLogTripleCluster
import GaloisForLFunctions.RHTower.CompleteResolutionCofinalConditioningLaw
import GaloisForLFunctions.HTGeometry.HilbertSchmidtMatrix

/-!
# Prime-normal Hilbert saturation at the complete Riemann-source horizon

For `p_i` the increasing sequence of primes, put

`P_j = (p_i ^ (-(j + 1)))_i ∈ ℓ²(ℕ, ℂ)`.

This file proves unconditionally:

* `P_j → 0` in `ℓ²`;
* the linear span of the `P_j` is norm dense;
* for every `y ∈ ℓ²`, the affine-difference span of `P_j - y` is norm dense;
* every norm-closed linear relation retaining these outputs along collapsing
  complete-source inputs has full vertical fibre and equals its domain times
  the whole Hilbert target;
* if such a relation is Hermitian, it is exactly the pure vertical relation
  `{0} × ℓ²`.

The density proof is constructive at the theorem level.  After rescaling
`P_j` by `p_k^(j+1)` and subtracting already recovered coordinates, the
remainder is `e_k` plus a tail whose norm decays geometrically at ratio
`p_k / p_(k+1) < 1`.
-/

open Complex Filter Topology
open scoped ENNReal

namespace RHTower

noncomputable section

/-- Canonical complex Hilbert target for square-summable prime-normal packets. -/
abbrev CompleteResolutionPrimeHilbertSpace := lp (fun _ : ℕ => ℂ) 2

theorem summable_completeResolutionPrimeHilbert_inv_norm_sq :
    Summable (fun i : ℕ => ‖((Nat.nth Nat.Prime i : ℂ)⁻¹)‖ ^ 2) := by
  have hp : Summable (fun p : Nat.Primes => ((p : ℝ)⁻¹) ^ 2) := by
    have h := Nat.Primes.summable_rpow.mpr (by norm_num : (-2 : ℝ) < -1)
    apply h.congr
    intro p
    rw [Real.rpow_neg (by positivity), Real.rpow_two]
    simp only [inv_pow]
  have hn : Summable
      (fun i : ℕ => (((nthPrimeEquiv i : Nat.Primes) : ℝ)⁻¹) ^ 2) :=
    nthPrimeEquiv.summable_iff.mpr hp
  apply hn.congr
  intro i
  simp [nthPrimeEquiv, nthPrimeSubtype, norm_inv]

theorem completeResolutionPrimeHilbert_inv_norm_le_one (i : ℕ) :
    ‖((Nat.nth Nat.Prime i : ℂ)⁻¹)‖ ≤ 1 := by
  rw [norm_inv, Complex.norm_natCast]
  have htwo : 2 ≤ Nat.nth Nat.Prime i :=
    (by omega : 2 ≤ i + 2).trans (Nat.add_two_le_nth_prime i)
  have hpos : (0 : ℝ) < Nat.nth Nat.Prime i := by positivity
  rw [inv_le_one₀ hpos]
  exact_mod_cast htwo.trans' (by omega : 1 ≤ 2)

theorem completeResolutionPrimeHilbert_inv_norm_le_half (i : ℕ) :
    ‖((Nat.nth Nat.Prime i : ℂ)⁻¹)‖ ≤ 1 / 2 := by
  rw [norm_inv, Complex.norm_natCast]
  have htwo : 2 ≤ Nat.nth Nat.Prime i :=
    (by omega : 2 ≤ i + 2).trans (Nat.add_two_le_nth_prime i)
  simpa [one_div] using
    (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
      (by exact_mod_cast htwo : (2 : ℝ) ≤ Nat.nth Nat.Prime i))

/-- The source-defined prime-normal packet `(p_i⁻¹)^(j+1)` in `ℓ²`. -/
def completeResolutionPrimeHilbertPacket (j : ℕ) : CompleteResolutionPrimeHilbertSpace :=
  ⟨fun i => ((Nat.nth Nat.Prime i : ℂ)⁻¹) ^ (j + 1), by
    apply memℓp_gen
    have hs : Summable
        (fun i : ℕ =>
          ‖((Nat.nth Nat.Prime i : ℂ)⁻¹) ^ (j + 1)‖ ^ 2) := by
      apply summable_completeResolutionPrimeHilbert_inv_norm_sq.of_nonneg_of_le
      · intro i
        positivity
      · intro i
        rw [norm_pow]
        have hq0 : 0 ≤ ‖((Nat.nth Nat.Prime i : ℂ)⁻¹)‖ := norm_nonneg _
        have hq1 := completeResolutionPrimeHilbert_inv_norm_le_one i
        have hpow :
            ‖((Nat.nth Nat.Prime i : ℂ)⁻¹)‖ ^ (j + 1) ≤
              ‖((Nat.nth Nat.Prime i : ℂ)⁻¹)‖ :=
          pow_le_of_le_one hq0 hq1 (by omega)
        exact (sq_le_sq₀ (pow_nonneg hq0 _) hq0).2 hpow
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hs⟩

def completeResolutionPrimeRatio (k i : ℕ) : ℝ :=
  (Nat.nth Nat.Prime k : ℝ) / (Nat.nth Nat.Prime i : ℝ)

theorem completeResolutionNthPrime_real_pos (i : ℕ) :
    0 < (Nat.nth Nat.Prime i : ℝ) := by
  exact_mod_cast (Nat.prime_nth_prime i).pos

theorem completeResolutionPrimeRatio_pos (k i : ℕ) :
    0 < completeResolutionPrimeRatio k i := by
  exact div_pos (completeResolutionNthPrime_real_pos k) (completeResolutionNthPrime_real_pos i)

theorem completeResolutionPrimeRatio_succ_lt_one (k : ℕ) :
    completeResolutionPrimeRatio k (k + 1) < 1 := by
  rw [completeResolutionPrimeRatio, div_lt_one (completeResolutionNthPrime_real_pos (k + 1))]
  exact_mod_cast nthPrimeSubtype_strictMono (Nat.lt_succ_self k)

theorem completeResolutionPrimeRatio_le_succ {k i : ℕ} (hi : k < i) :
    completeResolutionPrimeRatio k i ≤ completeResolutionPrimeRatio k (k + 1) := by
  rw [completeResolutionPrimeRatio, completeResolutionPrimeRatio]
  apply (div_le_div_iff_of_pos_left (completeResolutionNthPrime_real_pos k)
    (completeResolutionNthPrime_real_pos i) (completeResolutionNthPrime_real_pos (k + 1))).mpr
  exact_mod_cast nthPrimeSubtype_strictMono.monotone
    (Nat.succ_le_iff.mpr hi)

def completeResolutionPrimeHilbertTail (k j : ℕ) : CompleteResolutionPrimeHilbertSpace :=
  ⟨fun i =>
      if k < i then
        ((Nat.nth Nat.Prime k : ℂ) *
          (Nat.nth Nat.Prime i : ℂ)⁻¹) ^ (j + 1)
      else 0,
    by
      apply memℓp_gen
      have hscaled :
          Summable
            (fun i : ℕ =>
              ‖((Nat.nth Nat.Prime k : ℂ) ^ (j + 1) • completeResolutionPrimeHilbertPacket j) i‖ ^
                (2 : ENNReal).toReal) :=
        (lp.memℓp
          ((Nat.nth Nat.Prime k : ℂ) ^ (j + 1) • completeResolutionPrimeHilbertPacket j)).summable
          (by norm_num)
      apply hscaled.of_nonneg_of_le
      · intro i
        positivity
      · intro i
        by_cases hi : k < i
        · simp only [hi, if_true]
          change
            ‖((Nat.nth Nat.Prime k : ℂ) *
                (Nat.nth Nat.Prime i : ℂ)⁻¹) ^ (j + 1)‖ ^
                (2 : ENNReal).toReal ≤
              ‖(Nat.nth Nat.Prime k : ℂ) ^ (j + 1) *
                (Nat.nth Nat.Prime i : ℂ)⁻¹ ^ (j + 1)‖ ^
                (2 : ENNReal).toReal
          rw [mul_pow]
        · simp only [hi, if_false, norm_zero]
          rw [Real.zero_rpow (by norm_num :
            (2 : ENNReal).toReal ≠ 0)]
          exact Real.rpow_nonneg
            (norm_nonneg
              ((((Nat.nth Nat.Prime k : ℂ) ^ (j + 1)) •
                completeResolutionPrimeHilbertPacket j) i)) _⟩

@[simp] theorem completeResolutionPrimeHilbertTail_apply (k j i : ℕ) :
    completeResolutionPrimeHilbertTail k j i =
      if k < i then
        ((Nat.nth Nat.Prime k : ℂ) *
          (Nat.nth Nat.Prime i : ℂ)⁻¹) ^ (j + 1)
      else 0 := rfl

theorem completeResolutionPrimeHilbertTail_norm_le (k j : ℕ) :
    ‖completeResolutionPrimeHilbertTail k j‖ ≤
      (completeResolutionPrimeRatio k (k + 1)) ^ j * ‖completeResolutionPrimeHilbertTail k 0‖ := by
  calc
    ‖completeResolutionPrimeHilbertTail k j‖ ≤
        ‖((completeResolutionPrimeRatio k (k + 1) : ℂ) ^ j) • completeResolutionPrimeHilbertTail k 0‖ := by
      apply lp.norm_mono (by norm_num)
      intro i
      by_cases hi : k < i
      · change ‖completeResolutionPrimeHilbertTail k j i‖ ≤
          ‖((completeResolutionPrimeRatio k (k + 1) : ℂ) ^ j) * completeResolutionPrimeHilbertTail k 0 i‖
        rw [completeResolutionPrimeHilbertTail_apply, completeResolutionPrimeHilbertTail_apply, if_pos hi, if_pos hi]
        change
          ‖((Nat.nth Nat.Prime k : ℂ) *
              (Nat.nth Nat.Prime i : ℂ)⁻¹) ^ (j + 1)‖ ≤
            ‖((completeResolutionPrimeRatio k (k + 1) : ℂ) ^ j) *
              (((Nat.nth Nat.Prime k : ℂ) *
                (Nat.nth Nat.Prime i : ℂ)⁻¹) ^ (0 + 1))‖
        have hr0 : 0 ≤ completeResolutionPrimeRatio k (k + 1) :=
          (completeResolutionPrimeRatio_pos k (k + 1)).le
        have hri0 : 0 ≤ completeResolutionPrimeRatio k i :=
          (completeResolutionPrimeRatio_pos k i).le
        have hle := completeResolutionPrimeRatio_le_succ hi
        have hnorm :
            ‖(Nat.nth Nat.Prime k : ℂ) *
                (Nat.nth Nat.Prime i : ℂ)⁻¹‖ =
              completeResolutionPrimeRatio k i := by
          rw [norm_mul, norm_inv, Complex.norm_natCast,
            Complex.norm_natCast, completeResolutionPrimeRatio]
          rfl
        calc
          ‖((Nat.nth Nat.Prime k : ℂ) *
              (Nat.nth Nat.Prime i : ℂ)⁻¹) ^ (j + 1)‖ =
              (completeResolutionPrimeRatio k i) ^ (j + 1) := by
                rw [norm_pow, hnorm]
          _ ≤ (completeResolutionPrimeRatio k (k + 1)) ^ j *
                completeResolutionPrimeRatio k i := by
              rw [pow_succ]
              gcongr
          _ = ‖((completeResolutionPrimeRatio k (k + 1) : ℂ) ^ j) *
                (((Nat.nth Nat.Prime k : ℂ) *
                  (Nat.nth Nat.Prime i : ℂ)⁻¹) ^ (0 + 1))‖ := by
              rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
                abs_of_nonneg hr0, norm_pow, hnorm]
              simp
      · change ‖completeResolutionPrimeHilbertTail k j i‖ ≤
          ‖((completeResolutionPrimeRatio k (k + 1) : ℂ) ^ j) * completeResolutionPrimeHilbertTail k 0 i‖
        rw [completeResolutionPrimeHilbertTail_apply, completeResolutionPrimeHilbertTail_apply, if_neg hi, if_neg hi]
        simp
    _ = (completeResolutionPrimeRatio k (k + 1)) ^ j * ‖completeResolutionPrimeHilbertTail k 0‖ := by
      rw [norm_smul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (completeResolutionPrimeRatio_pos k (k + 1)).le]

theorem tendsto_completeResolutionPrimeHilbertTail_zero (k : ℕ) :
    Tendsto (completeResolutionPrimeHilbertTail k) atTop (nhds 0) := by
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  have hpow :=
    tendsto_pow_atTop_nhds_zero_of_lt_one
      (completeResolutionPrimeRatio_pos k (k + 1)).le
      (completeResolutionPrimeRatio_succ_lt_one k)
  have hbound :
      Tendsto
        (fun j : ℕ =>
          (completeResolutionPrimeRatio k (k + 1)) ^ j * ‖completeResolutionPrimeHilbertTail k 0‖)
        atTop (nhds 0) := by
    simpa using hpow.mul_const ‖completeResolutionPrimeHilbertTail k 0‖
  have hev :
      ∀ᶠ j : ℕ in atTop,
        (completeResolutionPrimeRatio k (k + 1)) ^ j * ‖completeResolutionPrimeHilbertTail k 0‖ < ε :=
    (tendsto_order.1 hbound).2 ε hε
  filter_upwards [hev] with j hj
  exact (completeResolutionPrimeHilbertTail_norm_le k j).trans_lt hj

def completeResolutionPrimeHilbertEarlier (k j : ℕ) : CompleteResolutionPrimeHilbertSpace :=
  ∑ i ∈ Finset.range k,
    (((Nat.nth Nat.Prime k : ℂ) *
      (Nat.nth Nat.Prime i : ℂ)⁻¹) ^ (j + 1)) •
      lp.single 2 i (1 : ℂ)

/-- Packet rescaling with all coordinates before `k` removed exactly. -/
def completeResolutionPrimeHilbertCorrected (k j : ℕ) : CompleteResolutionPrimeHilbertSpace :=
  ((Nat.nth Nat.Prime k : ℂ) ^ (j + 1)) • completeResolutionPrimeHilbertPacket j -
    completeResolutionPrimeHilbertEarlier k j

/-- The corrected packet is exactly the `k`-th basis vector plus a geometric tail. -/
theorem completeResolutionPrimeHilbertCorrected_eq_single_add_tail (k j : ℕ) :
    completeResolutionPrimeHilbertCorrected k j =
      lp.single 2 k (1 : ℂ) + completeResolutionPrimeHilbertTail k j := by
  ext i
  simp only [completeResolutionPrimeHilbertCorrected, completeResolutionPrimeHilbertEarlier, completeResolutionPrimeHilbertPacket, lp.coeFn_smul,
    Pi.smul_apply, smul_eq_mul, lp.coeFn_sub, Pi.sub_apply,
    lp.coeFn_sum, Finset.sum_apply, completeResolutionPrimeHilbertTail_apply, lp.coeFn_add,
    Pi.add_apply, lp.coeFn_single]
  simp_rw [mul_pow]
  by_cases hik : i < k
  · have hne : i ≠ k := Nat.ne_of_lt hik
    have hsum :
        (∑ x ∈ Finset.range k,
          (Nat.nth Nat.Prime k : ℂ) ^ (j + 1) *
            (Nat.nth Nat.Prime x : ℂ)⁻¹ ^ (j + 1) *
              (Pi.single x (1 : ℂ) : ℕ → ℂ) i) =
          (Nat.nth Nat.Prime k : ℂ) ^ (j + 1) *
            (Nat.nth Nat.Prime i : ℂ)⁻¹ ^ (j + 1) := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro b hb hbi
        rw [Pi.single_eq_of_ne hbi.symm]
        simp
      · simp [hik]
    rw [hsum]
    simp [hne, Nat.not_lt.mpr hik.le]
  · by_cases hki : k < i
    · have hne : i ≠ k := Nat.ne_of_gt hki
      have hsum :
          (∑ x ∈ Finset.range k,
            (Nat.nth Nat.Prime k : ℂ) ^ (j + 1) *
              (Nat.nth Nat.Prime x : ℂ)⁻¹ ^ (j + 1) *
                (Pi.single x (1 : ℂ) : ℕ → ℂ) i) = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        have hxi : x ≠ i := by
          have hxk := Finset.mem_range.mp hx
          omega
        rw [Pi.single_eq_of_ne hxi.symm]
        simp
      rw [hsum]
      simp [hki, hne]
    · have hieq : i = k := Nat.le_antisymm (Nat.not_lt.mp hki) (Nat.not_lt.mp hik)
      subst i
      have hprime : (Nat.nth Nat.Prime k : ℂ) ≠ 0 := by
        exact_mod_cast (Nat.prime_nth_prime k).ne_zero
      have hsum :
          (∑ x ∈ Finset.range k,
            (Nat.nth Nat.Prime k : ℂ) ^ (j + 1) *
              (Nat.nth Nat.Prime x : ℂ)⁻¹ ^ (j + 1) *
                (Pi.single x (1 : ℂ) : ℕ → ℂ) k) = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        have hxk := Finset.mem_range.mp hx
        have hxne : x ≠ k := Nat.ne_of_lt hxk
        rw [Pi.single_eq_of_ne hxne.symm]
        simp
      rw [hsum]
      simp [hprime]

theorem tendsto_completeResolutionPrimeHilbertCorrected_single (k : ℕ) :
    Tendsto (completeResolutionPrimeHilbertCorrected k) atTop
      (nhds (lp.single 2 k (1 : ℂ))) := by
  rw [show completeResolutionPrimeHilbertCorrected k =
      fun j => lp.single 2 k (1 : ℂ) + completeResolutionPrimeHilbertTail k j by
    funext j
    exact completeResolutionPrimeHilbertCorrected_eq_single_add_tail k j]
  simpa using (tendsto_const_nhds.add (tendsto_completeResolutionPrimeHilbertTail_zero k))

theorem completeResolutionPrimeHilbertPacket_norm_le (j : ℕ) :
    ‖completeResolutionPrimeHilbertPacket j‖ ≤ (1 / 2 : ℝ) ^ j * ‖completeResolutionPrimeHilbertPacket 0‖ := by
  calc
    ‖completeResolutionPrimeHilbertPacket j‖ ≤ ‖(((1 / 2 : ℝ) : ℂ) ^ j) • completeResolutionPrimeHilbertPacket 0‖ := by
      apply lp.norm_mono (by norm_num)
      intro i
      change
        ‖((Nat.nth Nat.Prime i : ℂ)⁻¹) ^ (j + 1)‖ ≤
          ‖(((1 / 2 : ℝ) : ℂ) ^ j) *
            ((Nat.nth Nat.Prime i : ℂ)⁻¹) ^ (0 + 1)‖
      have hq0 : 0 ≤ ‖((Nat.nth Nat.Prime i : ℂ)⁻¹)‖ :=
        norm_nonneg _
      have hqhalf := completeResolutionPrimeHilbert_inv_norm_le_half i
      calc
        ‖((Nat.nth Nat.Prime i : ℂ)⁻¹) ^ (j + 1)‖ =
            ‖((Nat.nth Nat.Prime i : ℂ)⁻¹)‖ ^ (j + 1) := by
              rw [norm_pow]
        _ ≤ (1 / 2 : ℝ) ^ j *
              ‖((Nat.nth Nat.Prime i : ℂ)⁻¹)‖ := by
            rw [pow_succ]
            gcongr
        _ = ‖(((1 / 2 : ℝ) : ℂ) ^ j) *
              ((Nat.nth Nat.Prime i : ℂ)⁻¹) ^ (0 + 1)‖ := by
            rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / 2)]
            simp
    _ = (1 / 2 : ℝ) ^ j * ‖completeResolutionPrimeHilbertPacket 0‖ := by
      rw [norm_smul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / 2)]

theorem tendsto_completeResolutionPrimeHilbertPacket_zero :
    Tendsto completeResolutionPrimeHilbertPacket atTop (nhds 0) := by
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  have hpow :
      Tendsto (fun j : ℕ => (1 / 2 : ℝ) ^ j) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)
  have hbound :
      Tendsto (fun j : ℕ => (1 / 2 : ℝ) ^ j * ‖completeResolutionPrimeHilbertPacket 0‖)
        atTop (nhds 0) := by
    simpa using hpow.mul_const ‖completeResolutionPrimeHilbertPacket 0‖
  have hev :
      ∀ᶠ j : ℕ in atTop,
        (1 / 2 : ℝ) ^ j * ‖completeResolutionPrimeHilbertPacket 0‖ < ε :=
    (tendsto_order.1 hbound).2 ε hε
  filter_upwards [hev] with j hj
  exact (completeResolutionPrimeHilbertPacket_norm_le j).trans_lt hj

/-- Algebraic span of all square-summable prime-normal packets. -/
def completeResolutionPrimeHilbertPacketSpan : Submodule ℂ CompleteResolutionPrimeHilbertSpace :=
  Submodule.span ℂ (Set.range completeResolutionPrimeHilbertPacket)

theorem completeResolutionPrimeHilbertCorrected_mem_packetSpan_closure
    {k : ℕ}
    (hprev : ∀ i < k,
      lp.single 2 i (1 : ℂ) ∈ completeResolutionPrimeHilbertPacketSpan.topologicalClosure)
    (j : ℕ) :
    completeResolutionPrimeHilbertCorrected k j ∈ completeResolutionPrimeHilbertPacketSpan.topologicalClosure := by
  apply Submodule.sub_mem
  · apply Submodule.smul_mem
    exact completeResolutionPrimeHilbertPacketSpan.le_topologicalClosure
      (Submodule.subset_span (Set.mem_range_self j))
  · unfold completeResolutionPrimeHilbertEarlier
    exact Submodule.sum_mem _ fun i hi =>
      Submodule.smul_mem _ _
        (hprev i (Finset.mem_range.mp hi))

theorem completeResolutionPrimeHilbert_single_mem_packetSpan_closure (k : ℕ) :
    lp.single 2 k (1 : ℂ) ∈ completeResolutionPrimeHilbertPacketSpan.topologicalClosure := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      apply (Submodule.isClosed_topologicalClosure completeResolutionPrimeHilbertPacketSpan).mem_of_tendsto
        (tendsto_completeResolutionPrimeHilbertCorrected_single k)
      exact Filter.Eventually.of_forall fun j =>
        completeResolutionPrimeHilbertCorrected_mem_packetSpan_closure ih j

/-- Prime-normal packets have norm-dense linear span in the Hilbert target. -/
theorem completeResolutionPrimeHilbertPacketSpan_closure_eq_top :
    completeResolutionPrimeHilbertPacketSpan.topologicalClosure = ⊤ := by
  let B : Submodule ℂ CompleteResolutionPrimeHilbertSpace :=
    Submodule.span ℂ
      (Set.range (HilbertSchmidt.lpBasis ℕ))
  have hB : B ≤ completeResolutionPrimeHilbertPacketSpan.topologicalClosure := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    rw [HilbertSchmidt.lpBasis_apply]
    exact completeResolutionPrimeHilbert_single_mem_packetSpan_closure k
  have hBclosure :
      B.topologicalClosure ≤ completeResolutionPrimeHilbertPacketSpan.topologicalClosure :=
    Submodule.topologicalClosure_minimal B hB
      (Submodule.isClosed_topologicalClosure completeResolutionPrimeHilbertPacketSpan)
  have hBdense : B.topologicalClosure = ⊤ := by
    exact (HilbertSchmidt.lpBasis ℕ).dense_span
  apply top_unique
  rw [← hBdense]
  exact hBclosure

/-- Span of all packets after subtracting an arbitrary proposed horizon value. -/
def completeResolutionPrimeHilbertAffinePacketSpan (y : CompleteResolutionPrimeHilbertSpace) :
    Submodule ℂ CompleteResolutionPrimeHilbertSpace :=
  Submodule.span ℂ (Set.range fun j : ℕ => completeResolutionPrimeHilbertPacket j - y)

theorem completeResolutionPrimeHilbertAffinePacketSpan_orthogonal_eq_bot (y : CompleteResolutionPrimeHilbertSpace) :
    (completeResolutionPrimeHilbertAffinePacketSpan y)ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro z hz
  have hdiff : ∀ j : ℕ, inner ℂ (completeResolutionPrimeHilbertPacket j - y) z = 0 := by
    intro j
    exact (Submodule.mem_orthogonal _ _).mp hz _
      (Submodule.subset_span (Set.mem_range_self j))
  have heq : ∀ j : ℕ, inner ℂ (completeResolutionPrimeHilbertPacket j) z = inner ℂ y z := by
    intro j
    have hj := hdiff j
    exact sub_eq_zero.mp (by simpa [inner_sub_left] using hj)
  have hleft :
      Tendsto (fun j : ℕ => inner ℂ (completeResolutionPrimeHilbertPacket j) z)
        atTop (nhds 0) := by
    simpa using tendsto_completeResolutionPrimeHilbertPacket_zero.inner
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => z) atTop (nhds z))
  have hyz : inner ℂ y z = 0 := by
    have hzero :
        Tendsto (fun _ : ℕ => inner ℂ y z) atTop (nhds 0) := by
      simpa only [heq] using hleft
    exact tendsto_nhds_unique tendsto_const_nhds hzero
  have hpacket : ∀ j : ℕ, inner ℂ (completeResolutionPrimeHilbertPacket j) z = 0 := by
    intro j
    rw [heq j, hyz]
  have hzunc : z ∈ completeResolutionPrimeHilbertPacketSpanᗮ := by
    rw [Submodule.mem_orthogonal]
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
        obtain ⟨j, rfl⟩ := hv
        exact hpacket j
    | zero => simp
    | add u v _ _ hu hv => simp [inner_add_left, hu, hv]
    | smul c v _ hv => simp [inner_smul_left, hv]
  have hzclosure : z ∈ completeResolutionPrimeHilbertPacketSpan.topologicalClosureᗮ := by
    simpa [Submodule.orthogonal_closure] using hzunc
  rw [completeResolutionPrimeHilbertPacketSpan_closure_eq_top,
    Submodule.top_orthogonal_eq_bot] at hzclosure
  exact hzclosure

/-- Arbitrary affine centering preserves norm density of the complete packet. -/
theorem completeResolutionPrimeHilbertAffinePacketSpan_closure_eq_top
    (y : CompleteResolutionPrimeHilbertSpace) :
    (completeResolutionPrimeHilbertAffinePacketSpan y).topologicalClosure = ⊤ := by
  calc
    (completeResolutionPrimeHilbertAffinePacketSpan y).topologicalClosure =
        (completeResolutionPrimeHilbertAffinePacketSpan y)ᗮᗮ :=
      (Submodule.orthogonal_orthogonal_eq_closure _).symm
    _ = (⊥ : Submodule ℂ CompleteResolutionPrimeHilbertSpace)ᗮ := by
      rw [completeResolutionPrimeHilbertAffinePacketSpan_orthogonal_eq_bot]
    _ = ⊤ := Submodule.bot_orthogonal_eq_top

/-- Any closed relation retaining affine prime packets along collapsing inputs
has the entire Hilbert target as its vertical fibre. -/
theorem closedLinearRelation_completeResolutionPrimeHilbert_fullVertical
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (R : Submodule ℂ (X × CompleteResolutionPrimeHilbertSpace))
    (hclosed : IsClosed (R : Set (X × CompleteResolutionPrimeHilbertSpace)))
    (u : ℕ → ℕ → X)
    (hu : ∀ j : ℕ, Tendsto (fun K : ℕ => u K j) atTop (nhds 0))
    (y : CompleteResolutionPrimeHilbertSpace)
    (hgraph : ∀ K j : ℕ, (u K j, completeResolutionPrimeHilbertPacket j - y) ∈ R)
    (z : CompleteResolutionPrimeHilbertSpace) :
    ((0 : X), z) ∈ R := by
  have hgenerators :
      ∀ j : ℕ, completeResolutionPrimeHilbertPacket j - y ∈ linearRelationVerticalFiber R := by
    intro j
    exact closedLinearRelation_mem_vertical_of_tendsto_zero
      R hclosed (fun K : ℕ => u K j) (completeResolutionPrimeHilbertPacket j - y)
      (hu j) (fun K => hgraph K j)
  have hspan :
      completeResolutionPrimeHilbertAffinePacketSpan y ≤ linearRelationVerticalFiber R := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact hgenerators j
  have hvclosed :
      IsClosed (linearRelationVerticalFiber R : Set CompleteResolutionPrimeHilbertSpace) := by
    change IsClosed
      ((fun v : CompleteResolutionPrimeHilbertSpace => ((0 : X), v)) ⁻¹' (R : Set (X × CompleteResolutionPrimeHilbertSpace)))
    exact hclosed.preimage (continuous_const.prodMk continuous_id)
  have hclosure :
      (completeResolutionPrimeHilbertAffinePacketSpan y).topologicalClosure ≤
        linearRelationVerticalFiber R :=
    Submodule.topologicalClosure_minimal
      (completeResolutionPrimeHilbertAffinePacketSpan y) hspan hvclosed
  change z ∈ linearRelationVerticalFiber R
  apply hclosure
  rw [completeResolutionPrimeHilbertAffinePacketSpan_closure_eq_top]
  trivial

/-- Full verticality factorizes the relation as its domain times the Hilbert target. -/
theorem closedLinearRelation_completeResolutionPrimeHilbert_eq_domain_prod
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (R : Submodule ℂ (X × CompleteResolutionPrimeHilbertSpace))
    (hclosed : IsClosed (R : Set (X × CompleteResolutionPrimeHilbertSpace)))
    (u : ℕ → ℕ → X)
    (hu : ∀ j : ℕ, Tendsto (fun K : ℕ => u K j) atTop (nhds 0))
    (y : CompleteResolutionPrimeHilbertSpace)
    (hgraph : ∀ K j : ℕ, (u K j, completeResolutionPrimeHilbertPacket j - y) ∈ R) :
    (R : Set (X × CompleteResolutionPrimeHilbertSpace)) =
      linearRelationDomain R ×ˢ Set.univ := by
  ext p
  constructor
  · intro hp
    exact ⟨⟨p.2, hp⟩, Set.mem_univ _⟩
  · rintro ⟨⟨v₀, hv₀⟩, _⟩
    have hv :
        ((0 : X), p.2 - v₀) ∈ R :=
      closedLinearRelation_completeResolutionPrimeHilbert_fullVertical
        R hclosed u hu y hgraph (p.2 - v₀)
    simpa using Submodule.add_mem R hv₀ hv

/-- The Hilbert packet is the positive-index part of the canonical countable reader. -/
theorem completeResolutionPrimeHilbertPacket_coe_eq_countablePrimeOutput (j : ℕ) :
    (completeResolutionPrimeHilbertPacket j : ℕ → ℂ) =
      completeResolutionCountablePrimeOutput (j + 1) := by
  rfl

/-- Complete-source specialization of Hilbert maximal verticality. -/
theorem completeResolution_closedLinearRelation_primeHilbert_affine_fullVertical
    (R : Submodule ℂ (CompleteResolutionSourceSpace × CompleteResolutionPrimeHilbertSpace))
    (hclosed :
      IsClosed (R : Set (CompleteResolutionSourceSpace × CompleteResolutionPrimeHilbertSpace)))
    (y : CompleteResolutionPrimeHilbertSpace)
    (hgraph : ∀ K j : ℕ,
      (completeResolutionCountablePrimeInput K (j + 1),
        completeResolutionPrimeHilbertPacket j - y) ∈ R)
    (z : CompleteResolutionPrimeHilbertSpace) :
    ((0 : CompleteResolutionSourceSpace), z) ∈ R := by
  exact closedLinearRelation_completeResolutionPrimeHilbert_fullVertical R hclosed
    (fun K j => completeResolutionCountablePrimeInput K (j + 1))
    (fun j => tendsto_completeResolutionCountablePrimeInput_zero (j + 1))
    y hgraph z

/-- Complete-source Hilbert relation retains no output constraint. -/
theorem completeResolution_closedLinearRelation_primeHilbert_affine_eq_domain_prod
    (R : Submodule ℂ (CompleteResolutionSourceSpace × CompleteResolutionPrimeHilbertSpace))
    (hclosed :
      IsClosed (R : Set (CompleteResolutionSourceSpace × CompleteResolutionPrimeHilbertSpace)))
    (y : CompleteResolutionPrimeHilbertSpace)
    (hgraph : ∀ K j : ℕ,
      (completeResolutionCountablePrimeInput K (j + 1),
        completeResolutionPrimeHilbertPacket j - y) ∈ R) :
    (R : Set (CompleteResolutionSourceSpace × CompleteResolutionPrimeHilbertSpace)) =
      linearRelationDomain R ×ˢ Set.univ := by
  exact closedLinearRelation_completeResolutionPrimeHilbert_eq_domain_prod R hclosed
    (fun K j => completeResolutionCountablePrimeInput K (j + 1))
    (fun j => tendsto_completeResolutionCountablePrimeInput_zero (j + 1))
    y hgraph

/-- Symmetry condition for a complex Hilbert-space linear relation. -/
def IsHermitianLinearRelation
    (R : Submodule ℂ (CompleteResolutionPrimeHilbertSpace × CompleteResolutionPrimeHilbertSpace)) : Prop :=
  ∀ ⦃x v x' v' : CompleteResolutionPrimeHilbertSpace⦄,
    (x, v) ∈ R → (x', v') ∈ R →
      inner ℂ v x' = inner ℂ x v'

/-- A Hermitian closed relation retaining the complete affine packet is pure vertical. -/
theorem closedHermitianRelation_completeResolutionPrimeHilbert_eq_pureVertical
    (R : Submodule ℂ (CompleteResolutionPrimeHilbertSpace × CompleteResolutionPrimeHilbertSpace))
    (hclosed : IsClosed (R : Set (CompleteResolutionPrimeHilbertSpace × CompleteResolutionPrimeHilbertSpace)))
    (u : ℕ → ℕ → CompleteResolutionPrimeHilbertSpace)
    (hu : ∀ j : ℕ, Tendsto (fun K : ℕ => u K j) atTop (nhds 0))
    (y : CompleteResolutionPrimeHilbertSpace)
    (hgraph : ∀ K j : ℕ, (u K j, completeResolutionPrimeHilbertPacket j - y) ∈ R)
    (hsymm : IsHermitianLinearRelation R) :
    (R : Set (CompleteResolutionPrimeHilbertSpace × CompleteResolutionPrimeHilbertSpace)) =
      ({0} : Set CompleteResolutionPrimeHilbertSpace) ×ˢ Set.univ := by
  ext p
  constructor
  · intro hp
    have hv : ((0 : CompleteResolutionPrimeHilbertSpace), p.1) ∈ R :=
      closedLinearRelation_completeResolutionPrimeHilbert_fullVertical
        R hclosed u hu y hgraph p.1
    have hinner : inner ℂ p.1 p.1 = 0 := by
      simpa using (hsymm hp hv).symm
    exact ⟨inner_self_eq_zero.mp hinner, Set.mem_univ _⟩
  · rintro ⟨hp, _⟩
    have hpzero : p.1 = 0 := Set.mem_singleton_iff.mp hp
    change (p.1, p.2) ∈ R
    rw [hpzero]
    exact closedLinearRelation_completeResolutionPrimeHilbert_fullVertical
      R hclosed u hu y hgraph p.2

end

end RHTower
