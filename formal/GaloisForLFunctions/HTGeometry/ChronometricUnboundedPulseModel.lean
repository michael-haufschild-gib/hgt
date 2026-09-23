import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import GaloisForLFunctions.HTGeometry.ChronometricRegularPulseTomography

/-!
# A regular pulse family with a genuinely unbounded generator

The recovery theorem for regular families assumes only that the generators are linear maps of a
common invariant domain. This file shows the hypothesis class really does contain unbounded
generators, so the theorem is not a disguised Banach-algebra statement.

The model is the diagonal one: bounded sequences with the supremum norm, the domain of finitely
supported sequences, pulses given by multiplication with the unimodular sequence `k ↦ e^{itk}`, and
generators given by multiplication with the unbounded sequence `k ↦ k`. The pulses are bounded
operators of norm one; the generator is not bounded at all.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BoundedContinuousFunction
open Asymptotics

/-- Bounded complex sequences with the supremum norm. -/
abbrev BoundedSeq := ℕ →ᵇ ℂ

/-- The common invariant domain: finitely supported bounded sequences. -/
def finiteSupportSeq : Submodule ℂ BoundedSeq where
  carrier := {f | ∃ N : ℕ, ∀ k, N ≤ k → f k = 0}
  add_mem' := by
    rintro f g ⟨N, hN⟩ ⟨M, hM⟩
    refine ⟨max N M, fun k hk => ?_⟩
    rw [BoundedContinuousFunction.add_apply, hN k (le_trans (le_max_left _ _) hk),
      hM k (le_trans (le_max_right _ _) hk), add_zero]
  zero_mem' := ⟨0, fun k _ => rfl⟩
  smul_mem' := by
    rintro c f ⟨N, hN⟩
    exact ⟨N, fun k hk => by
      rw [BoundedContinuousFunction.smul_apply, hN k hk, smul_zero]⟩

theorem mem_finiteSupportSeq_iff (f : BoundedSeq) :
    f ∈ finiteSupportSeq ↔ ∃ N : ℕ, ∀ k, N ≤ k → f k = 0 := Iff.rfl

/-! ### The unbounded diagonal generator -/

theorem norm_natMul_le (f : BoundedSeq) (N : ℕ) (hN : ∀ k, N ≤ k → f k = 0) (k : ℕ) :
    ‖(k : ℂ) * f k‖ ≤ (N : ℝ) * ‖f‖ := by
  rcases le_or_gt N k with h | h
  · rw [hN k h, mul_zero, norm_zero]
    positivity
  · rw [norm_mul, Complex.norm_natCast]
    exact mul_le_mul (by exact_mod_cast h.le) (f.norm_coe_le_norm k) (norm_nonneg _)
      (Nat.cast_nonneg _)

/-- Multiplication by the unbounded sequence `k ↦ k`, on the finitely supported domain. -/
noncomputable def natWeight (f : finiteSupportSeq) : BoundedSeq :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun k => (k : ℂ) * (f : BoundedSeq) k) continuous_of_discreteTopology
    ((Classical.choose f.2 : ℕ) * ‖(f : BoundedSeq)‖)
    (norm_natMul_le _ _ (Classical.choose_spec f.2))

@[simp] theorem natWeight_apply (f : finiteSupportSeq) (k : ℕ) :
    natWeight f k = (k : ℂ) * (f : BoundedSeq) k := rfl

theorem natWeight_mem (f : finiteSupportSeq) : natWeight f ∈ finiteSupportSeq := by
  obtain ⟨N, hN⟩ := f.2
  exact ⟨N, fun k hk => by rw [natWeight_apply, hN k hk, mul_zero]⟩

/-- The diagonal generator as a linear endomorphism of the domain. -/
noncomputable def natGenerator : finiteSupportSeq →ₗ[ℂ] finiteSupportSeq where
  toFun f := ⟨natWeight f, natWeight_mem f⟩
  map_add' f g := by
    refine Subtype.ext (BoundedContinuousFunction.ext fun k => ?_)
    simp only [natWeight_apply, Submodule.coe_add, BoundedContinuousFunction.add_apply]
    ring
  map_smul' c f := by
    refine Subtype.ext (BoundedContinuousFunction.ext fun k => ?_)
    simp only [natWeight_apply, SetLike.val_smul, BoundedContinuousFunction.smul_apply,
      RingHom.id_apply, smul_eq_mul]
    ring

@[simp] theorem natGenerator_coe (f : finiteSupportSeq) :
    ((natGenerator f : finiteSupportSeq) : BoundedSeq) = natWeight f := rfl

/-! ### The unimodular diagonal pulses -/

/-- The unimodular phase sequence `k ↦ e^{itk}`. -/
private noncomputable def phaseSeq (t : ℝ) : BoundedSeq :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun k => Complex.exp (Complex.I * (t * k : ℝ))) continuous_of_discreteTopology 1
    (fun k => by
      rw [Complex.norm_exp]
      simp)

@[simp] theorem phaseSeq_apply (t : ℝ) (k : ℕ) :
    phaseSeq t k = Complex.exp (Complex.I * (t * k : ℝ)) := rfl

/-- The controlled clock pulse: multiplication by the unimodular phase sequence. -/
noncomputable def natPulse (t : ℝ) : BoundedSeq →L[ℂ] BoundedSeq :=
  (ContinuousLinearMap.mul ℂ BoundedSeq) (phaseSeq t)

@[simp] theorem natPulse_apply (t : ℝ) (f : BoundedSeq) (k : ℕ) :
    natPulse t f k = Complex.exp (Complex.I * (t * k : ℝ)) * f k := by
  simp [natPulse]

theorem natPulse_zero (f : BoundedSeq) : natPulse 0 f = f := by
  refine BoundedContinuousFunction.ext fun k => ?_
  rw [natPulse_apply]
  norm_num

/-! ### The regular-family derivative property -/

theorem hasDerivAt_natPulse (f : finiteSupportSeq) :
    HasDerivAt (fun t : ℝ => natPulse t (f : BoundedSeq))
      (Complex.I • ((natGenerator f : finiteSupportSeq) : BoundedSeq)) 0 := by
  obtain ⟨N, hN⟩ := f.2
  rw [hasDerivAt_iff_isLittleO]
  have hrw :
      (fun t : ℝ => natPulse t (f : BoundedSeq) - natPulse 0 (f : BoundedSeq) -
          (t - 0) • (Complex.I • natWeight f)) =
        fun t : ℝ =>
          natPulse t (f : BoundedSeq) - (f : BoundedSeq) - t • (Complex.I • natWeight f) := by
    funext t
    rw [natPulse_zero, sub_zero]
  have hbound : ∀ t : ℝ, |t| * (N : ℝ) ≤ 1 →
      ‖natPulse t (f : BoundedSeq) - (f : BoundedSeq) - t • (Complex.I • natWeight f)‖ ≤
        ((N : ℝ) ^ (2 : ℕ) * ‖(f : BoundedSeq)‖) * ‖t ^ (2 : ℕ)‖ := by
    intro t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)]
    refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun k => ?_
    have hval :
        (natPulse t (f : BoundedSeq) - (f : BoundedSeq) - t • (Complex.I • natWeight f)) k =
          (Complex.exp (Complex.I * (t * k : ℝ)) - 1 - Complex.I * (t * k : ℝ)) *
            (f : BoundedSeq) k := by
      simp only [BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.smul_apply,
        natPulse_apply, natWeight_apply, smul_eq_mul, Complex.real_smul]
      push_cast
      ring
    rw [hval, norm_mul]
    rcases le_or_gt N k with hk | hk
    · rw [hN k hk, norm_zero, mul_zero]
      positivity
    · have hz : ‖Complex.I * ((t * k : ℝ) : ℂ)‖ = |t| * (k : ℝ) := by
        rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
          Nat.abs_cast]
      have hkN : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hk.le
      have hzle : ‖Complex.I * ((t * k : ℝ) : ℂ)‖ ≤ 1 := by
        rw [hz]
        exact le_trans (by nlinarith [abs_nonneg t, Nat.cast_nonneg (α := ℝ) k]) ht
      have hexp := Complex.norm_exp_sub_one_sub_id_le hzle
      rw [hz] at hexp
      have hfk : ‖(f : BoundedSeq) k‖ ≤ ‖(f : BoundedSeq)‖ :=
        BoundedContinuousFunction.norm_coe_le_norm _ k
      calc ‖Complex.exp (Complex.I * ((t * k : ℝ) : ℂ)) - 1 - Complex.I * ((t * k : ℝ) : ℂ)‖ *
            ‖(f : BoundedSeq) k‖
          ≤ (|t| * (k : ℝ)) ^ (2 : ℕ) * ‖(f : BoundedSeq)‖ := by
            exact mul_le_mul hexp hfk (norm_nonneg _) (by positivity)
        _ ≤ ((N : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ)) * ‖(f : BoundedSeq)‖ := by
            refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
            have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
            have hsq : (|t| * (k : ℝ)) ^ (2 : ℕ) = t ^ (2 : ℕ) * (k : ℝ) ^ (2 : ℕ) := by
              rw [mul_pow, sq_abs]
            have hk2 : (k : ℝ) ^ (2 : ℕ) ≤ (N : ℝ) ^ (2 : ℕ) := by nlinarith [hkN, hk0]
            rw [hsq]
            nlinarith [mul_nonneg (sq_nonneg t) (sub_nonneg.mpr hk2)]
        _ = ((N : ℝ) ^ (2 : ℕ) * ‖(f : BoundedSeq)‖) * t ^ (2 : ℕ) := by ring
  have hball : ∀ᶠ t : ℝ in nhds 0,
      ‖natPulse t (f : BoundedSeq) - (f : BoundedSeq) - t • (Complex.I • natWeight f)‖ ≤
        ((N : ℝ) ^ (2 : ℕ) * ‖(f : BoundedSeq)‖) * ‖t ^ (2 : ℕ)‖ := by
    have hmem : Metric.ball (0 : ℝ) (1 / ((N : ℝ) + 1)) ∈ nhds (0 : ℝ) :=
      Metric.ball_mem_nhds _ (by positivity)
    filter_upwards [hmem] with t ht
    refine hbound t ?_
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
    have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have : |t| * ((N : ℝ) + 1) < 1 := by
      rw [lt_div_iff₀ hN1] at ht
      linarith
    nlinarith [abs_nonneg t, Nat.cast_nonneg (α := ℝ) N]
  rw [natGenerator_coe, hrw]
  simp only [sub_zero]
  exact (IsBigO.of_bound _ hball).trans_isLittleO
    (isLittleO_pow_id (𝕜 := ℝ) (n := 2) one_lt_two)

/-! ### The generator is genuinely unbounded -/

/-- The unit sequence supported at `k`. -/
noncomputable def natUnit (k : ℕ) : BoundedSeq :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun j => if j = k then (1 : ℂ) else 0) continuous_of_discreteTopology 1
    (fun j => by by_cases h : j = k <;> simp [h])

@[simp] theorem natUnit_apply (k j : ℕ) :
    natUnit k j = if j = k then (1 : ℂ) else 0 := rfl

theorem natUnit_mem (k : ℕ) : natUnit k ∈ finiteSupportSeq :=
  ⟨k + 1, fun j hj => by
    have : j ≠ k := by omega
    simp [natUnit_apply, this]⟩

theorem norm_natUnit (k : ℕ) : ‖natUnit k‖ = 1 := by
  refine le_antisymm ((BoundedContinuousFunction.norm_le zero_le_one).2 fun j => ?_) ?_
  · by_cases h : j = k <;> simp [natUnit_apply, h]
  · have := BoundedContinuousFunction.norm_coe_le_norm (natUnit k) k
    simpa [natUnit_apply] using this

theorem le_norm_natWeight_natUnit (k : ℕ) :
    (k : ℝ) ≤ ‖natWeight ⟨natUnit k, natUnit_mem k⟩‖ := by
  have := BoundedContinuousFunction.norm_coe_le_norm
    (natWeight ⟨natUnit k, natUnit_mem k⟩) k
  simpa [natWeight_apply, natUnit_apply] using this

/-- **The diagonal generator is not a bounded operator.** No constant controls its norm on the
domain, so the regular-family hypotheses are strictly weaker than membership of a Banach algebra. -/
theorem natGenerator_unbounded :
    ¬ ∃ C : ℝ, ∀ f : finiteSupportSeq,
      ‖((natGenerator f : finiteSupportSeq) : BoundedSeq)‖ ≤ C * ‖(f : BoundedSeq)‖ := by
  rintro ⟨C, hC⟩
  obtain ⟨k, hk⟩ := exists_nat_gt C
  have hbound := hC ⟨natUnit k, natUnit_mem k⟩
  rw [natGenerator_coe] at hbound
  have hnorm : ‖((⟨natUnit k, natUnit_mem k⟩ : finiteSupportSeq) : BoundedSeq)‖ = 1 :=
    norm_natUnit k
  rw [hnorm, mul_one] at hbound
  exact absurd (le_trans (le_norm_natWeight_natUnit k) hbound) (not_le.mpr hk)

/-- **A regular pulse family with unbounded generators exists.** The ordered-correlation recovery
theorem therefore applies to genuinely unbounded generators. -/
theorem exists_unbounded_regularPulseFamily (n : ℕ) :
    ∃ (pulse : Fin n → ℝ → (BoundedSeq →L[ℂ] BoundedSeq))
      (gen : Fin n → (finiteSupportSeq →ₗ[ℂ] finiteSupportSeq)),
      (∀ (j : Fin n) (v : finiteSupportSeq),
        HasDerivAt (fun t : ℝ => pulse j t (v : BoundedSeq))
          (Complex.I • ((gen j v : finiteSupportSeq) : BoundedSeq)) 0) ∧
      ∀ j : Fin n, ¬ ∃ C : ℝ, ∀ f : finiteSupportSeq,
        ‖((gen j f : finiteSupportSeq) : BoundedSeq)‖ ≤ C * ‖(f : BoundedSeq)‖ :=
  ⟨fun _ => natPulse, fun _ => natGenerator, fun _ v => hasDerivAt_natPulse v,
    fun _ => natGenerator_unbounded⟩

end GaloisForLFunctions.HTGeometry
