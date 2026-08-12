import GaloisForLFunctions.RHTower.MobiusThetaInternalJetPrimeNormalComplexGraph

/-!
# Exact Möbius prime-normal successor blow-up

This module constructs the singular cross-index transport between complete physical
Möbius--theta residuals.  For every positive ordinary integer `p`, `mobiusSuccessor p` is the
first later integer with nonzero Möbius coefficient.  At every honest depth `m ≥ 3`, the literal
`L²(R)` source identity is

`T (Rₚ,ₘ - μ(p) Θ) = Rᵣ,ₘ`.

The proof transports the complete convergent tail.  It does not replace the source by a scalar
Dirichlet series or specialize at a Xi divisor.  The concrete `2 → 3` graph has vertical limit
`(0, -Θ)`, cannot be contained in a sequentially closable ambient operator, and its operator norm
diverges with the exact exponential factor `(3/2)^(m/2)`.  Its reflected spectral normalizers
have radial ratio `((r/p)^(m(2 Re(s)-1)))`, equal to one exactly on the critical wall.

No Xi-zero location, RH premise, numerical computation, or nonstandard axiom is used.
-/

open scoped ArithmeticFunction
open Filter MeasureTheory

namespace RHTower

noncomputable section

theorem exists_mobius_ne_zero_gt (p : ℕ) :
    ∃ n : ℕ, p < n ∧ ArithmeticFunction.moebius n ≠ 0 := by
  obtain ⟨q, hpq, hq⟩ := Nat.exists_infinite_primes (p + 1)
  refine ⟨q, by omega, ?_⟩
  rw [ArithmeticFunction.moebius_apply_prime hq]
  norm_num

/-- First ordinary integer strictly beyond `p` with nonzero Möbius coefficient. -/
noncomputable def mobiusSuccessor (p : ℕ) : ℕ :=
  Nat.find (exists_mobius_ne_zero_gt p)

theorem lt_mobiusSuccessor (p : ℕ) : p < mobiusSuccessor p :=
  (Nat.find_spec (exists_mobius_ne_zero_gt p)).1

theorem moebius_mobiusSuccessor_ne_zero (p : ℕ) :
    ArithmeticFunction.moebius (mobiusSuccessor p) ≠ 0 :=
  (Nat.find_spec (exists_mobius_ne_zero_gt p)).2

theorem moebius_eq_zero_of_lt_mobiusSuccessor
    {p n : ℕ} (hpn : p < n) (hn : n < mobiusSuccessor p) :
    ArithmeticFunction.moebius n = 0 := by
  by_contra hne
  have hmin := Nat.find_min' (exists_mobius_ne_zero_gt p) ⟨hpn, hne⟩
  exact (Nat.not_lt_of_ge hmin) hn

theorem mobiusSuccessor_pos {p : ℕ} (hp : 1 ≤ p) : 0 < mobiusSuccessor p :=
  lt_of_lt_of_le (by omega) (Nat.le_of_lt (lt_mobiusSuccessor p))

theorem mobiusSuccessor_two : mobiusSuccessor 2 = 3 := by
  apply Nat.le_antisymm
  · exact Nat.find_min' (exists_mobius_ne_zero_gt 2) (by
      constructor
      · omega
      · rw [ArithmeticFunction.moebius_apply_prime Nat.prime_three]
        norm_num)
  · have h := lt_mobiusSuccessor 2
    omega

abbrev MobiusPositiveIndex := {p : ℕ // 1 ≤ p}

abbrev MobiusHonestDepth := {m : ℕ // 3 ≤ m}

theorem additiveTranslationUnitary_add_apply (a b : ℝ) (f : MobiusThetaSourceL2) :
    MellinL2.additiveTranslationUnitary a
        (MellinL2.additiveTranslationUnitary b f) =
      MellinL2.additiveTranslationUnitary (a + b) f := by
  change Lp.compMeasurePreserving (MellinL2.realTranslationEquiv a)
      (MellinL2.realTranslation_measurePreserving a)
      (Lp.compMeasurePreserving (MellinL2.realTranslationEquiv b)
        (MellinL2.realTranslation_measurePreserving b) f) =
    Lp.compMeasurePreserving (MellinL2.realTranslationEquiv (a + b))
      (MellinL2.realTranslation_measurePreserving (a + b)) f
  rw [← Lp.compMeasurePreserving_comp_apply]
  apply Lp.ext
  filter_upwards [
    Lp.coeFn_compMeasurePreserving f
      ((MellinL2.realTranslation_measurePreserving b).comp
        (MellinL2.realTranslation_measurePreserving a)),
    Lp.coeFn_compMeasurePreserving f
      (MellinL2.realTranslation_measurePreserving (a + b))
  ] with x hx hy
  rw [hx, hy]
  simp [MellinL2.realTranslationEquiv, Function.comp_apply]

/-- Exact singular transport from a positive index to its first nonzero Möbius successor. -/
def mobiusThetaSuccessorBlowup
    (p : MobiusPositiveIndex) (m : ℕ) (f : MobiusThetaSourceL2) :
    MobiusThetaSourceL2 :=
  (((((mobiusSuccessor p : ℝ) / p) ^ ((m : ℝ) / 2) : ℝ) : ℂ)) •
    MellinL2.additiveTranslationUnitary
      (((m : ℝ) * Real.log ((mobiusSuccessor p : ℝ) / p)) *
        MellinL2.spectralNormalization) f

/-- Bundled continuous-linear form of the successor blow-up. -/
def mobiusThetaSuccessorBlowupCLM
    (p : MobiusPositiveIndex) (m : ℕ) :
    MobiusThetaSourceL2 →L[ℂ] MobiusThetaSourceL2 :=
  ((((mobiusSuccessor p : ℝ) / p) ^ ((m : ℝ) / 2) : ℝ) : ℂ) •
    (MellinL2.additiveTranslationUnitary
      (((m : ℝ) * Real.log ((mobiusSuccessor p : ℝ) / p)) *
        MellinL2.spectralNormalization)).toLinearIsometry.toContinuousLinearMap

@[simp] theorem mobiusThetaSuccessorBlowupCLM_apply
    (p : MobiusPositiveIndex) (m : ℕ) (f : MobiusThetaSourceL2) :
    mobiusThetaSuccessorBlowupCLM p m f = mobiusThetaSuccessorBlowup p m f := by
  rfl

theorem summable_mobiusThetaPrimeNormalTailTerm
    {p m : ℕ} (hp : 1 ≤ p) (hm : 3 ≤ m) :
    Summable (mobiusThetaPrimeNormalTailTerm p m) := by
  exact (summable_mobiusThetaPrimeNormalMajorant p).of_norm_bounded (fun k =>
    norm_mobiusThetaPrimeNormalTailTerm_le_majorant hp hm k)

private theorem successor_ratio_mul_ratio
    (p : MobiusPositiveIndex) (n : ℕ) (hn : 0 < n) :
    (mobiusSuccessor p : ℝ) / n =
      ((mobiusSuccessor p : ℝ) / p) * ((p : ℝ) / n) := by
  have hp0 : (p : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : (p : ℕ) ≠ 0)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  field_simp [hp0, hn0]

private theorem successor_translation_identity
    (p : MobiusPositiveIndex) (m n : ℕ) (hn : 0 < n) :
    (m : ℝ) * Real.log ((mobiusSuccessor p : ℝ) / p) *
          MellinL2.spectralNormalization +
        -((m : ℝ) * Real.log ((n : ℝ) / p)) *
          MellinL2.spectralNormalization =
      -((m : ℝ) * Real.log ((n : ℝ) / mobiusSuccessor p)) *
        MellinL2.spectralNormalization := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.2
  have hr0 : (0 : ℝ) < mobiusSuccessor p := by
    exact_mod_cast mobiusSuccessor_pos p.2
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.log_div (ne_of_gt hr0) (ne_of_gt hp0),
    Real.log_div (ne_of_gt hn0) (ne_of_gt hp0),
    Real.log_div (ne_of_gt hn0) (ne_of_gt hr0)]
  ring

theorem mobiusThetaSuccessorBlowup_tail_head
    (p : MobiusPositiveIndex) (m : ℕ) :
    mobiusThetaSuccessorBlowup p m
        (mobiusThetaPrimeNormalTailTerm p m (mobiusSuccessor p - p - 1)) =
      (((ArithmeticFunction.moebius (mobiusSuccessor p) : ℝ) : ℂ)) •
        xiThetaSourceL2 := by
  rw [mobiusThetaSuccessorBlowup, mobiusThetaPrimeNormalTailTerm, map_smul,
    smul_smul, additiveTranslationUnitary_add_apply]
  have hindex : p + (mobiusSuccessor p - p - 1) + 1 = mobiusSuccessor p := by
    have := lt_mobiusSuccessor p
    omega
  rw [hindex]
  have htranslate0 :
      (m : ℝ) * Real.log ((mobiusSuccessor p : ℝ) / p) *
            MellinL2.spectralNormalization +
          -((m : ℝ) * Real.log ((mobiusSuccessor p : ℝ) / p)) *
            MellinL2.spectralNormalization = 0 := by ring
  rw [htranslate0]
  have hunit : MellinL2.additiveTranslationUnitary 0 xiThetaSourceL2 =
      xiThetaSourceL2 := by
    change Lp.compMeasurePreserving (MellinL2.realTranslationEquiv 0)
      (MellinL2.realTranslation_measurePreserving 0) xiThetaSourceL2 = xiThetaSourceL2
    apply Lp.ext
    filter_upwards [Lp.coeFn_compMeasurePreserving xiThetaSourceL2
      (MellinL2.realTranslation_measurePreserving 0)] with x hx
    rw [hx]
    simp [MellinL2.realTranslationEquiv, Function.comp_apply]
  rw [hunit]
  congr 1
  rw [mobiusThetaPrimeNormalWeight, hindex]
  have hreal : ((mobiusSuccessor p : ℝ) / p) ^ ((m : ℝ) / 2) *
      ((p : ℝ) / mobiusSuccessor p) ^ ((m : ℝ) / 2) = 1 := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    have hp0 : (p : ℝ) ≠ 0 := by
      exact_mod_cast (by omega : (p : ℕ) ≠ 0)
    have hr0 : (mobiusSuccessor p : ℝ) ≠ 0 := by
      exact_mod_cast ne_of_gt (mobiusSuccessor_pos p.2)
    have : ((mobiusSuccessor p : ℝ) / p) *
        ((p : ℝ) / mobiusSuccessor p) = 1 := by field_simp [hp0, hr0]
    rw [this]
    simp
  push_cast
  norm_cast
  calc
    ((mobiusSuccessor p : ℝ) / p) ^ ((m : ℝ) / 2) *
          ((ArithmeticFunction.moebius (mobiusSuccessor p) : ℝ) *
            ((p : ℝ) / mobiusSuccessor p) ^ ((m : ℝ) / 2)) =
        (ArithmeticFunction.moebius (mobiusSuccessor p) : ℝ) *
          (((mobiusSuccessor p : ℝ) / p) ^ ((m : ℝ) / 2) *
            ((p : ℝ) / mobiusSuccessor p) ^ ((m : ℝ) / 2)) := by ring
    _ = _ := by rw [hreal, mul_one]

theorem mobiusThetaSuccessorBlowup_tail_succ
    (p : MobiusPositiveIndex) (m k : ℕ) :
    mobiusThetaSuccessorBlowup p m
        (mobiusThetaPrimeNormalTailTerm p m
          (mobiusSuccessor p - p - 1 + (k + 1))) =
      mobiusThetaPrimeNormalTailTerm (mobiusSuccessor p) m k := by
  rw [mobiusThetaSuccessorBlowup, mobiusThetaPrimeNormalTailTerm, map_smul,
    smul_smul, additiveTranslationUnitary_add_apply]
  have hindex :
      p + (mobiusSuccessor p - p - 1 + (k + 1)) + 1 =
        mobiusSuccessor p + k + 1 := by
    have := lt_mobiusSuccessor p
    omega
  rw [hindex]
  have hn : 0 < mobiusSuccessor p + k + 1 := by positivity
  have hratio := successor_ratio_mul_ratio p (mobiusSuccessor p + k + 1) hn
  have hcoeff :
      ((mobiusSuccessor p : ℝ) / p) ^ ((m : ℝ) / 2) *
          mobiusThetaPrimeNormalWeight p m
            (mobiusSuccessor p - p - 1 + (k + 1)) =
        mobiusThetaPrimeNormalWeight (mobiusSuccessor p) m k := by
    rw [mobiusThetaPrimeNormalWeight, mobiusThetaPrimeNormalWeight, hindex]
    rw [hratio, Real.mul_rpow (by positivity) (by positivity)]
    ring
  have htranslate := successor_translation_identity p m
    (mobiusSuccessor p + k + 1) hn
  congr 1
  · exact_mod_cast hcoeff
  · exact congrArg
      (fun t => MellinL2.additiveTranslationUnitary t xiThetaSourceL2) htranslate

theorem mobiusThetaPrimeNormalTailTerm_eq_zero_before_successor
    (p : MobiusPositiveIndex) (m k : ℕ)
    (hk : k < mobiusSuccessor p - p - 1) :
    mobiusThetaPrimeNormalTailTerm p m k = 0 := by
  rw [mobiusThetaPrimeNormalTailTerm, mobiusThetaPrimeNormalWeight]
  have hpn : p < p + k + 1 := by omega
  have hnr : p + k + 1 < mobiusSuccessor p := by
    have := lt_mobiusSuccessor p
    omega
  rw [moebius_eq_zero_of_lt_mobiusSuccessor hpn hnr]
  simp

private theorem mobiusThetaSuccessorBlowup_prefix_sum
    (p : MobiusPositiveIndex) (m : ℕ) :
    (∑ k ∈ Finset.range (mobiusSuccessor p - p - 1 + 1),
        mobiusThetaSuccessorBlowup p m
          (mobiusThetaPrimeNormalTailTerm p m k)) =
      (((ArithmeticFunction.moebius (mobiusSuccessor p) : ℝ) : ℂ)) •
        xiThetaSourceL2 := by
  let d := mobiusSuccessor p - p - 1
  rw [Finset.sum_eq_single d]
  · exact mobiusThetaSuccessorBlowup_tail_head p m
  · intro b hb hbd
    have hb_lt : b < mobiusSuccessor p - p - 1 := by
      simp only [Finset.mem_range] at hb
      omega
    rw [mobiusThetaPrimeNormalTailTerm_eq_zero_before_successor p m b hb_lt]
    simp [mobiusThetaSuccessorBlowup]
  · simp [d]

/-- Exact transport of the complete physical tail from `p` to its first nonzero Möbius
successor.  Positivity and honest convergence depth are encoded in the input types. -/
theorem mobiusTheta_successor_transport
    (p : MobiusPositiveIndex) (m : MobiusHonestDepth) :
    mobiusThetaSuccessorBlowup p m
        (mobiusThetaPrimeNormalResidual p m -
          (((ArithmeticFunction.moebius p : ℝ) : ℂ)) • xiThetaSourceL2) =
      mobiusThetaPrimeNormalResidual (mobiusSuccessor p) m := by
  rw [mobiusThetaPrimeNormalResidual, mobiusThetaPrimeNormalResidual]
  have hcancel :
      (((ArithmeticFunction.moebius p : ℝ) : ℂ)) • xiThetaSourceL2 +
          (∑' k : ℕ, mobiusThetaPrimeNormalTailTerm p m k) -
          (((ArithmeticFunction.moebius p : ℝ) : ℂ)) • xiThetaSourceL2 =
        ∑' k : ℕ, mobiusThetaPrimeNormalTailTerm p m k := by abel
  rw [hcancel, ← mobiusThetaSuccessorBlowupCLM_apply]
  have hs := summable_mobiusThetaPrimeNormalTailTerm p.2 m.2
  rw [ContinuousLinearMap.map_tsum (mobiusThetaSuccessorBlowupCLM p m) hs]
  have hsmap : Summable (fun k : ℕ =>
      mobiusThetaSuccessorBlowupCLM p m
        (mobiusThetaPrimeNormalTailTerm p m k)) :=
    hs.mapL (mobiusThetaSuccessorBlowupCLM p m)
  rw [← hsmap.sum_add_tsum_nat_add (mobiusSuccessor p - p - 1 + 1)]
  simp only [mobiusThetaSuccessorBlowupCLM_apply]
  rw [mobiusThetaSuccessorBlowup_prefix_sum]
  congr 1
  apply tsum_congr
  intro k
  have hindex : k + (mobiusSuccessor p - p - 1 + 1) =
      mobiusSuccessor p - p - 1 + (k + 1) := by omega
  rw [hindex]
  exact mobiusThetaSuccessorBlowup_tail_succ p m k

/-- Fixed `2 → 3` successor blow-up, retained as a named concrete source operator. -/
def mobiusThetaTwoThreeSuccessorBlowup
    (m : ℕ) (f : MobiusThetaSourceL2) : MobiusThetaSourceL2 :=
  mobiusThetaSuccessorBlowup ⟨2, by omega⟩ m f

/-- Exact complete-source `2 → 3` identity. -/
theorem mobiusTheta_two_three_successor_transport (m : MobiusHonestDepth) :
    mobiusThetaTwoThreeSuccessorBlowup m
        (mobiusThetaPrimeNormalResidual 2 m + xiThetaSourceL2) =
      mobiusThetaPrimeNormalResidual 3 m := by
  have h := mobiusTheta_successor_transport (p := ⟨2, by omega⟩) m
  simpa [mobiusThetaTwoThreeSuccessorBlowup, mobiusSuccessor_two,
    ArithmeticFunction.moebius_apply_prime Nat.prime_two] using h

/-- Cofinal source leg of the exact `2 → 3` graph. -/
def mobiusThetaTwoThreeCofinalSource (n : ℕ) : MobiusThetaSourceL2 :=
  mobiusThetaPrimeNormalResidual 2 (n + 3) + xiThetaSourceL2

/-- Cofinal output leg, defined by the actual singular successor transport. -/
def mobiusThetaTwoThreeCofinalTarget (n : ℕ) : MobiusThetaSourceL2 :=
  mobiusThetaTwoThreeSuccessorBlowup (n + 3)
    (mobiusThetaTwoThreeCofinalSource n)

theorem mobiusThetaTwoThreeCofinalTarget_eq (n : ℕ) :
    mobiusThetaTwoThreeCofinalTarget n =
      mobiusThetaPrimeNormalResidual 3 (n + 3) := by
  exact mobiusTheta_two_three_successor_transport ⟨n + 3, by omega⟩

theorem tendsto_mobiusThetaTwoThreeCofinalSource_zero :
    Tendsto mobiusThetaTwoThreeCofinalSource atTop (nhds 0) := by
  have h := (tendsto_mobiusThetaPrimeNormalResidual_of_prime Nat.prime_two).comp
    (tendsto_add_atTop_nat 3)
  have hconst : Tendsto (fun _ : ℕ => xiThetaSourceL2) atTop
      (nhds xiThetaSourceL2) := tendsto_const_nhds
  change Tendsto
    (fun n : ℕ => mobiusThetaPrimeNormalResidual 2 (n + 3) + xiThetaSourceL2)
    atTop (nhds 0)
  simpa only [Function.comp_apply, neg_add_cancel] using h.add hconst

theorem tendsto_mobiusThetaTwoThreeCofinalTarget :
    Tendsto mobiusThetaTwoThreeCofinalTarget atTop (nhds (-xiThetaSourceL2)) := by
  have h := (tendsto_mobiusThetaPrimeNormalResidual_of_prime Nat.prime_three).comp
    (tendsto_add_atTop_nat 3)
  exact h.congr' (Filter.Eventually.of_forall fun n =>
    (mobiusThetaTwoThreeCofinalTarget_eq n).symm)

theorem xiThetaSourceL2_ne_zero : xiThetaSourceL2 ≠ 0 := by
  intro hzero
  have horbit (a : ℝ) : xiThetaTranslationOrbit a ∈
      (⊥ : Submodule ℂ MobiusThetaSourceL2) := by
    simp [xiThetaTranslationOrbit, hzero]
  have hclosed : IsClosed ((⊥ : Submodule ℂ MobiusThetaSourceL2) :
      Set MobiusThetaSourceL2) := by
    rw [show ((⊥ : Submodule ℂ MobiusThetaSourceL2) : Set MobiusThetaSourceL2) =
        {0} by ext x; simp]
    exact isClosed_singleton
  have hbot : (⊥ : Submodule ℂ MobiusThetaSourceL2) = ⊤ :=
    closedSubmodule_eq_top_of_isCyclicFamily
      isCyclicFamily_xiThetaTranslationOrbit ⊥ hclosed horbit
  exact (bot_ne_top : (⊥ : Submodule ℂ MobiusThetaSourceL2) ≠ ⊤) hbot

/-- Sequential closability for an algebraic operator on the ambient physical `L²`. -/
def MobiusThetaSequentiallyClosable
    (T : MobiusThetaSourceL2 →ₗ[ℂ] MobiusThetaSourceL2) : Prop :=
  ∀ u : ℕ → MobiusThetaSourceL2,
    Tendsto u atTop (nhds 0) →
    ∀ y : MobiusThetaSourceL2,
      Tendsto (fun n => T (u n)) atTop (nhds y) → y = 0

/-- A single algebraic operator containing every point of the cofinal successor graph. -/
structure MobiusThetaTwoThreeGraphExtension where
  toLinearMap : MobiusThetaSourceL2 →ₗ[ℂ] MobiusThetaSourceL2
  map_cofinalSource : ∀ n : ℕ,
    toLinearMap (mobiusThetaTwoThreeCofinalSource n) =
      mobiusThetaTwoThreeCofinalTarget n

/-- No sequentially closable ambient operator contains the exact cofinal successor graph. -/
theorem MobiusThetaTwoThreeGraphExtension.not_sequentiallyClosable
    (T : MobiusThetaTwoThreeGraphExtension) :
    ¬ MobiusThetaSequentiallyClosable T.toLinearMap := by
  intro hclose
  have htarget : Tendsto
      (fun n => T.toLinearMap (mobiusThetaTwoThreeCofinalSource n))
      atTop (nhds (-xiThetaSourceL2)) := by
    exact tendsto_mobiusThetaTwoThreeCofinalTarget.congr'
      (Filter.Eventually.of_forall fun n => (T.map_cofinalSource n).symm)
  have hvertical := hclose mobiusThetaTwoThreeCofinalSource
    tendsto_mobiusThetaTwoThreeCofinalSource_zero (-xiThetaSourceL2) htarget
  exact (neg_ne_zero.mpr xiThetaSourceL2_ne_zero) hvertical

private theorem one_lt_mobiusSuccessor_ratio (p : MobiusPositiveIndex) :
    1 < (mobiusSuccessor p : ℝ) / p := by
  rw [one_lt_div (by exact_mod_cast (by omega : 0 < (p : ℕ)))]
  exact_mod_cast lt_mobiusSuccessor p

/-- Exact norm of every singular successor transport. -/
theorem norm_mobiusThetaSuccessorBlowupCLM
    (p : MobiusPositiveIndex) (m : ℕ) :
    ‖mobiusThetaSuccessorBlowupCLM p m‖ =
      ((mobiusSuccessor p : ℝ) / p) ^ ((m : ℝ) / 2) := by
  rw [mobiusThetaSuccessorBlowupCLM, norm_smul,
    LinearIsometry.norm_toContinuousLinearMap, mul_one,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos (lt_trans zero_lt_one
      (one_lt_mobiusSuccessor_ratio p)) _)]

/-- Exponential blow-up is explicit: successor-operator norms diverge along honest depths. -/
theorem tendsto_norm_mobiusThetaSuccessorBlowupCLM_atTop
    (p : MobiusPositiveIndex) :
    Tendsto (fun n : ℕ => ‖mobiusThetaSuccessorBlowupCLM p (n + 3)‖)
      atTop atTop := by
  simp_rw [norm_mobiusThetaSuccessorBlowupCLM,
    Real.rpow_def_of_pos (lt_trans zero_lt_one (one_lt_mobiusSuccessor_ratio p))]
  apply Real.tendsto_exp_atTop.comp
  have hlog : 0 < Real.log ((mobiusSuccessor p : ℝ) / p) :=
    Real.log_pos (one_lt_mobiusSuccessor_ratio p)
  have hshift : Tendsto (fun n : ℕ => ((n + 3 : ℕ) : ℝ)) atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 3)
  have hhalf : Tendsto (fun n : ℕ => ((n + 3 : ℕ) : ℝ) / 2) atTop atTop :=
    hshift.atTop_div_const (by norm_num)
  exact hhalf.const_mul_atTop hlog

/-- Complex spectral normalizer of successor transport. -/
def mobiusThetaSuccessorSpectralNormalizer
    (p : MobiusPositiveIndex) (m : ℕ) (s : ℂ) : ℂ :=
  (((mobiusSuccessor p : ℝ) / p : ℝ) : ℂ) ^ ((m : ℂ) * s)

/-- Reflected complex spectral normalizer, with analytic dagger `s ↦ 1 - conj s`. -/
def mobiusThetaSuccessorReflectedSpectralNormalizer
    (p : MobiusPositiveIndex) (m : ℕ) (s : ℂ) : ℂ :=
  (((mobiusSuccessor p : ℝ) / p : ℝ) : ℂ) ^
    ((m : ℂ) * (1 - starRingEnd ℂ s))

/-- Exact radial reflection anomaly of the successor transport. -/
theorem mobiusThetaSuccessorSpectralNormalizer_norm_ratio
    (p : MobiusPositiveIndex) (m : ℕ) (s : ℂ) :
    ‖mobiusThetaSuccessorSpectralNormalizer p m s‖ /
        ‖mobiusThetaSuccessorReflectedSpectralNormalizer p m s‖ =
      ((mobiusSuccessor p : ℝ) / p) ^ ((m : ℝ) * (2 * s.re - 1)) := by
  have hbase : 0 < (mobiusSuccessor p : ℝ) / p :=
    lt_trans zero_lt_one (one_lt_mobiusSuccessor_ratio p)
  rw [mobiusThetaSuccessorSpectralNormalizer,
    mobiusThetaSuccessorReflectedSpectralNormalizer,
    Complex.norm_cpow_eq_rpow_re_of_pos hbase,
    Complex.norm_cpow_eq_rpow_re_of_pos hbase,
    ← Real.rpow_sub hbase]
  congr 1
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    zero_mul, sub_zero, Complex.sub_re, Complex.one_re, Complex.conj_re]
  ring

/-- Reflected successor compatibility occurs exactly on the critical wall. -/
theorem mobiusThetaSuccessorSpectralNormalizer_norm_ratio_eq_one_iff
    (p : MobiusPositiveIndex) (m : MobiusHonestDepth) (s : ℂ) :
    ‖mobiusThetaSuccessorSpectralNormalizer p m s‖ /
        ‖mobiusThetaSuccessorReflectedSpectralNormalizer p m s‖ = 1 ↔
      s.re = 1 / 2 := by
  rw [mobiusThetaSuccessorSpectralNormalizer_norm_ratio]
  have hbase : 0 < (mobiusSuccessor p : ℝ) / p :=
    lt_trans zero_lt_one (one_lt_mobiusSuccessor_ratio p)
  rw [Real.rpow_def_of_pos hbase, Real.exp_eq_one_iff]
  have hlog : Real.log ((mobiusSuccessor p : ℝ) / p) ≠ 0 :=
    ne_of_gt (Real.log_pos (one_lt_mobiusSuccessor_ratio p))
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : (m : ℕ) ≠ 0)
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · exact (hlog h).elim
    · rcases mul_eq_zero.mp h with h | h
      · exact (hm h).elim
      · linarith
  · intro hs
    rw [hs]
    ring

private theorem mobiusSuccessor_cpow_mul_index_cpow
    (p : MobiusPositiveIndex) (z : ℂ) :
    ((((mobiusSuccessor p : ℝ) / p : ℝ) : ℂ) ^ z) * ((p : ℂ) ^ z) =
      (mobiusSuccessor p : ℂ) ^ z := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast p.2
  have hrR : (0 : ℝ) < mobiusSuccessor p := by
    exact_mod_cast mobiusSuccessor_pos p.2
  have haR : (0 : ℝ) < (mobiusSuccessor p : ℝ) / p := div_pos hrR hpR
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr haR.ne'),
    Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr (by omega : (p : ℕ) ≠ 0)),
    Complex.cpow_def_of_ne_zero
      (Nat.cast_ne_zero.mpr (ne_of_gt (mobiusSuccessor_pos p.2))), ← Complex.exp_add]
  congr 1
  have hlogp : Complex.log (p : ℂ) = (Real.log (p : ℝ) : ℂ) := by
    exact (Complex.ofReal_log hpR.le).symm
  have hlogr : Complex.log (mobiusSuccessor p : ℂ) =
      (Real.log (mobiusSuccessor p : ℝ) : ℂ) := by
    exact (Complex.ofReal_log hrR.le).symm
  have hloga : Complex.log (((mobiusSuccessor p : ℝ) / p : ℝ) : ℂ) =
      (Real.log ((mobiusSuccessor p : ℝ) / p) : ℂ) := by
    exact (Complex.ofReal_log haR.le).symm
  rw [hloga, hlogp, hlogr, Real.log_div (ne_of_gt hrR) (ne_of_gt hpR)]
  push_cast
  ring

private theorem mobiusThetaSuccessorSpectralCoefficient_transport
    (p : MobiusPositiveIndex) (m : ℕ) (w : ℂ) (k : ℕ) :
    mobiusThetaSuccessorSpectralNormalizer p m (mobiusThetaCenteredParameter w) *
        mobiusThetaPrimeNormalResidualSpectralCoefficient p m w
          (mobiusSuccessor p - p + k) =
      mobiusThetaPrimeNormalResidualSpectralCoefficient
        (mobiusSuccessor p) m w k := by
  have hindex : p + (mobiusSuccessor p - p + k) = mobiusSuccessor p + k := by
    have := lt_mobiusSuccessor p
    omega
  rw [mobiusThetaSuccessorSpectralNormalizer,
    mobiusThetaPrimeNormalResidualSpectralCoefficient,
    mobiusThetaPrimeNormalResidualSpectralCoefficient, hindex]
  rw [← mul_assoc, mobiusSuccessor_cpow_mul_index_cpow]

end

end RHTower
