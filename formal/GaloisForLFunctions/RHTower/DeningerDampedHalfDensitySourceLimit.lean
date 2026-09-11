import GaloisForLFunctions.RHTower.DeningerDampedPrimeMellinGrowth
import GaloisForLFunctions.RHTower.L2MellinUnitary
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Actual damped prime sources in half-density L²

The literal exponential-weight embedding conjugates original Meyer translation
with its exact scalar. At half density, the damped prime defect and its
weighted-reflection mate become an adjoint pair of unitary-translation defects.
The original finite-prime Gaussian sources therefore obey quantitative upper,
lower and successive-difference bounds in actual unquotiented L².

For every fixed damping `a > 1/2`, the prime weights are summable. The original
all-primes-up-to-N sources converge in L², with a summable-tail error bound.
The positive convergent product of lower factors and nonzero original Gaussian
prove that the limit is nonzero. Damping one gives a closed concrete instance.

No source incidence, RH premise, numerical experiment or probability
renormalization is used. This constructs the actual vector limit; weighted
Mellin admission, the complete original Green/BV boundary, fixed physical
reader comparison, and continuation to zero damping remain separate problems.
-/

open Complex Filter Topology SchwartzMap MeasureTheory
noncomputable section
namespace RHTower

abbrev DeningerHalfDensityL2 := Lp (α := ℝ) ℂ 2

def deningerStrongLogWeightedSchwartzLM (c : ℝ) :
    DeningerMeyerStrongLogTarget →ₗ[ℂ] 𝓢(ℝ, ℂ) :=
  (deningerExpMulSchwartzLM c).comp deningerDampedStrongLogOriginalSourceLM

theorem deningerStrongLogWeightedSchwartzLM_apply (c : ℝ)
    (g : DeningerMeyerStrongLogTarget) (t : ℝ) :
    deningerStrongLogWeightedSchwartzLM c g t =
      (Real.exp (c*t) : ℂ) * g.val t := rfl

def deningerStrongLogWeightedL2LM (c : ℝ) :
    DeningerMeyerStrongLogTarget →ₗ[ℂ] DeningerHalfDensityL2 :=
  (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ)).toLinearMap.comp
    (deningerStrongLogWeightedSchwartzLM c)

theorem deningerStrongLogWeightedL2LM_flow (c d : ℝ)
    (g : DeningerMeyerStrongLogTarget) :
    deningerStrongLogWeightedL2LM c (deningerMeyerStrongLogFlow d g) =
      (Real.exp (c*d) : ℂ) • MellinL2.additiveTranslationUnitary (-d)
        (deningerStrongLogWeightedL2LM c g) := by
  change (deningerStrongLogWeightedSchwartzLM c (deningerMeyerStrongLogFlow d g)).toLp 2 volume = _
  rw [show deningerStrongLogWeightedL2LM c g =
    (deningerStrongLogWeightedSchwartzLM c g).toLp 2 volume by rfl,
    MellinL2.additiveTranslation_toLp]
  change (SchwartzMap.toLpCLM ℂ ℂ 2 volume) _ =
    (Real.exp (c*d) : ℂ) • (SchwartzMap.toLpCLM ℂ ℂ 2 volume) _
  rw [← map_smul]
  congr 1
  ext t
  simp only [deningerStrongLogWeightedSchwartzLM_apply, deningerMeyerStrongLogFlow_apply,
    smul_apply, MellinL2.schwartzTranslate_apply, smul_eq_mul]
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  simp only [sub_eq_add_neg]
  rw [show c*d+c*(t + -d) = c*t by ring]

def deningerHalfDensityPrimeFactor (L a : ℝ) :
    DeningerHalfDensityL2 →L[ℂ] DeningerHalfDensityL2 :=
  ContinuousLinearMap.id ℂ _ - (Real.exp (-(a+1/2)*L) : ℂ) •
    (MellinL2.additiveTranslationUnitary L).toLinearIsometry.toContinuousLinearMap

def deningerHalfDensityPrimeMate (L a : ℝ) :
    DeningerHalfDensityL2 →L[ℂ] DeningerHalfDensityL2 :=
  ContinuousLinearMap.id ℂ _ - (Real.exp (-(a+1/2)*L) : ℂ) •
    (MellinL2.additiveTranslationUnitary (-L)).toLinearIsometry.toContinuousLinearMap

def deningerHalfDensityPairedPrime (L a : ℝ) :
    DeningerHalfDensityL2 →L[ℂ] DeningerHalfDensityL2 :=
  (deningerHalfDensityPrimeFactor L a).comp (deningerHalfDensityPrimeMate L a)

theorem deningerStrongLogHalfDensity_factor (L a : ℝ)
    (g : DeningerMeyerStrongLogTarget) :
    deningerStrongLogWeightedL2LM (1/2) (deningerDampedStrongLogDefect L a g) =
      deningerHalfDensityPrimeFactor L a (deningerStrongLogWeightedL2LM (1/2) g) := by
  change deningerStrongLogWeightedL2LM (1/2)
    (g - (deningerDampedPrimeWeight L a : ℂ) • deningerMeyerStrongLogFlow (-L) g) = _
  rw [map_sub, map_smul, deningerStrongLogWeightedL2LM_flow, smul_smul]
  simp only [deningerHalfDensityPrimeFactor, sub_apply,
    ContinuousLinearMap.id_apply, smul_apply, neg_neg]
  congr 2
  rw [deningerDampedPrimeWeight, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  ring

theorem deningerStrongLogHalfDensity_mate (L a : ℝ)
    (g : DeningerMeyerStrongLogTarget) :
    deningerStrongLogWeightedL2LM (1/2)
      (deningerMeyerStrongLogJ (deningerDampedStrongLogDefect L a (deningerMeyerStrongLogJ g))) =
      deningerHalfDensityPrimeMate L a (deningerStrongLogWeightedL2LM (1/2) g) := by
  rw [deningerDampedStrongLogDefect_J_mate, map_sub, map_smul,
    deningerStrongLogWeightedL2LM_flow, smul_smul]
  simp only [deningerHalfDensityPrimeMate, sub_apply,
    ContinuousLinearMap.id_apply, smul_apply]
  congr 2
  rw [deningerDampedPrimeWeight, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
    ← Real.exp_add, ← Real.exp_add]
  congr 2
  ring

theorem deningerStrongLogHalfDensity_paired (L a : ℝ)
    (g : DeningerMeyerStrongLogTarget) :
    deningerStrongLogWeightedL2LM (1/2) (deningerDampedPairedStrongLogDefect L a g) =
      deningerHalfDensityPairedPrime L a (deningerStrongLogWeightedL2LM (1/2) g) := by
  change deningerStrongLogWeightedL2LM (1/2)
    (deningerDampedStrongLogDefect L a (deningerMeyerStrongLogJ
      (deningerDampedStrongLogDefect L a (deningerMeyerStrongLogJ g)))) = _
  rw [deningerStrongLogHalfDensity_factor, deningerStrongLogHalfDensity_mate]
  rfl

private theorem deningerUnitaryDefect_norm_bounds
    (U : DeningerHalfDensityL2 ≃ₗᵢ[ℂ] DeningerHalfDensityL2)
    {w : ℝ} (hw : 0 ≤ w) (f : DeningerHalfDensityL2) :
    (1-w)*‖f‖ ≤ ‖f - (w : ℂ) • U f‖ ∧
      ‖f - (w : ℂ) • U f‖ ≤ (1+w)*‖f‖ := by
  have heq : ‖(w : ℂ) • U f‖ = w * ‖f‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw,
      LinearIsometryEquiv.norm_map]
  constructor
  · have h := norm_sub_norm_le f ((w : ℂ) • U f)
    rw [heq] at h
    nlinarith
  · have h := norm_sub_le f ((w : ℂ) • U f)
    rw [heq] at h
    nlinarith

theorem deningerHalfDensityPairedPrime_norm_bounds
    (L a : ℝ) (hw : Real.exp (-(a+1/2)*L) ≤ 1) (f : DeningerHalfDensityL2) :
    (1-Real.exp (-(a+1/2)*L))^2 * ‖f‖ ≤ ‖deningerHalfDensityPairedPrime L a f‖ ∧
    ‖deningerHalfDensityPairedPrime L a f‖ ≤ Real.exp (2*Real.exp (-(a+1/2)*L)) * ‖f‖ := by
  let w := Real.exp (-(a+1/2)*L)
  have hw0 : 0 ≤ w := (Real.exp_pos _).le
  have hM := deningerUnitaryDefect_norm_bounds (MellinL2.additiveTranslationUnitary (-L)) hw0 f
  have hD := deningerUnitaryDefect_norm_bounds (MellinL2.additiveTranslationUnitary L) hw0
    (deningerHalfDensityPrimeMate L a f)
  change (1-w)*‖f‖ ≤ ‖deningerHalfDensityPrimeMate L a f‖ ∧
    ‖deningerHalfDensityPrimeMate L a f‖ ≤ (1+w)*‖f‖ at hM
  change (1-w)*‖deningerHalfDensityPrimeMate L a f‖ ≤ ‖deningerHalfDensityPairedPrime L a f‖ ∧
    ‖deningerHalfDensityPairedPrime L a f‖ ≤ (1+w)*‖deningerHalfDensityPrimeMate L a f‖ at hD
  constructor
  · calc
      (1-w)^2 * ‖f‖ = (1-w)*((1-w)*‖f‖) := by ring
      _ ≤ (1-w)*‖deningerHalfDensityPrimeMate L a f‖ :=
        mul_le_mul_of_nonneg_left hM.1 (sub_nonneg.mpr hw)
      _ ≤ _ := hD.1
  · have hexp : 1+w ≤ Real.exp w := by linarith [Real.add_one_le_exp w]
    calc
      ‖deningerHalfDensityPairedPrime L a f‖ ≤ (1+w)*((1+w)*‖f‖) :=
        hD.2.trans (mul_le_mul_of_nonneg_left hM.2 (by positivity))
      _ ≤ Real.exp w * (Real.exp w * ‖f‖) := by gcongr
      _ = Real.exp (2*w) * ‖f‖ := by rw [← mul_assoc, ← Real.exp_add]; congr 2; ring

theorem deningerHalfDensityPairedPrime_increment
    (L a : ℝ) (hw : Real.exp (-(a+1/2)*L) ≤ 1) (f : DeningerHalfDensityL2) :
    ‖deningerHalfDensityPairedPrime L a f - f‖ ≤
      3 * Real.exp (-(a+1/2)*L) * ‖f‖ := by
  let w := Real.exp (-(a+1/2)*L)
  have hw0 : 0 ≤ w := (Real.exp_pos _).le
  have hm := (deningerUnitaryDefect_norm_bounds
    (MellinL2.additiveTranslationUnitary (-L)) hw0 f).2
  change ‖deningerHalfDensityPrimeMate L a f‖ ≤ (1+w)*‖f‖ at hm
  have hD : ‖deningerHalfDensityPairedPrime L a f - deningerHalfDensityPrimeMate L a f‖ =
      w * ‖deningerHalfDensityPrimeMate L a f‖ := by
    change ‖(deningerHalfDensityPrimeMate L a f - (w : ℂ) •
      MellinL2.additiveTranslationUnitary L (deningerHalfDensityPrimeMate L a f)) -
        deningerHalfDensityPrimeMate L a f‖ = _
    rw [sub_sub_cancel_left, norm_neg, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hw0, LinearIsometryEquiv.norm_map]
  have hM : ‖deningerHalfDensityPrimeMate L a f - f‖ = w*‖f‖ := by
    change ‖(f - (w : ℂ) • MellinL2.additiveTranslationUnitary (-L) f) - f‖ = _
    rw [sub_sub_cancel_left, norm_neg, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hw0, LinearIsometryEquiv.norm_map]
  calc
    ‖deningerHalfDensityPairedPrime L a f - f‖ ≤
        ‖deningerHalfDensityPairedPrime L a f - deningerHalfDensityPrimeMate L a f‖ +
          ‖deningerHalfDensityPrimeMate L a f - f‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = w*‖deningerHalfDensityPrimeMate L a f‖ + w*‖f‖ := by rw [hD,hM]
    _ ≤ w*((1+w)*‖f‖)+w*‖f‖ := by gcongr
    _ ≤ 3*w*‖f‖ := by nlinarith [mul_nonneg (mul_nonneg hw0 (sub_nonneg.mpr hw)) (norm_nonneg f)]

def deningerHalfDensityPrimeStepWeight (a : ℝ) (n : ℕ) : ℝ :=
  if n.Prime then (n : ℝ)^(-(a+1/2)) else 0

theorem deningerHalfDensityPrimeStepWeight_nonneg (a : ℝ) (n : ℕ) :
    0 ≤ deningerHalfDensityPrimeStepWeight a n := by
  unfold deningerHalfDensityPrimeStepWeight
  split_ifs <;> positivity

theorem deningerHalfDensityPrimeStepWeight_lt_one {a : ℝ} (ha : 1/2 < a) (n : ℕ) :
    deningerHalfDensityPrimeStepWeight a n < 1 := by
  unfold deningerHalfDensityPrimeStepWeight
  split_ifs with hn
  · exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hn.one_lt) (by linarith)
  · norm_num

theorem deningerHalfDensityPrimeStepWeight_summable {a : ℝ} (ha : 1/2 < a) :
    Summable (deningerHalfDensityPrimeStepWeight a) := by
  apply Summable.of_nonneg_of_le (deningerHalfDensityPrimeStepWeight_nonneg a)
    (fun n => ?_) (Real.summable_nat_rpow.mpr (by linarith : -(a+1/2) < -1))
  unfold deningerHalfDensityPrimeStepWeight
  split_ifs
  · exact le_rfl
  · positivity

theorem deningerHalfDensityPrimeStepWeight_eq_exp (a : ℝ) (p : Nat.Primes) :
    deningerHalfDensityPrimeStepWeight a p = Real.exp (-(a+1/2)*Real.log (p : ℕ)) := by
  rw [deningerHalfDensityPrimeStepWeight, if_pos p.property,
    Real.rpow_def_of_pos (by exact_mod_cast p.property.pos)]
  congr 1
  ring

private theorem deningerDampedPrimeListSource_finset_insert
    (a : ℝ) (P : Finset Nat.Primes) (p : Nat.Primes) (hp : p ∉ P) :
    deningerDampedPrimeListSource a (insert p P).toList =
      deningerDampedPairedStrongLogDefect (Real.log (p : ℕ)) a
        (deningerDampedPrimeListSource a P.toList) := by
  apply deningerMeyerStrongLogMellin_injective
  funext s
  dsimp only
  rw [deningerDampedPairedStrongLogDefect_mellin, deningerDampedPrimeListSource_mellin,
    deningerDampedPrimeListSource_mellin]
  simp only [deningerDampedPrimeListMultiplier, Finset.prod_map_toList, Finset.prod_insert hp]
  ring

private theorem deningerDampedPrimePrefix_source_step (a : ℝ) (n : ℕ) :
    deningerDampedPrimeListSource a (GaloisForLFunctions.primesLE (n+1)).toList =
      if (n+1).Prime then
        deningerDampedPairedStrongLogDefect (Real.log ((n+1 : ℕ) : ℝ)) a
          (deningerDampedPrimeListSource a (GaloisForLFunctions.primesLE n).toList)
      else deningerDampedPrimeListSource a (GaloisForLFunctions.primesLE n).toList := by
  classical
  split_ifs with hn
  · let p : Nat.Primes := ⟨n+1,hn⟩
    have hP : GaloisForLFunctions.primesLE (n+1) = insert p (GaloisForLFunctions.primesLE n) := by
      ext q
      simp only [GaloisForLFunctions.mem_primesLE, Finset.mem_insert]
      have heq : q = p ↔ (q : ℕ) = n+1 := Subtype.ext_iff
      rw [heq]
      omega
    rw [hP, deningerDampedPrimeListSource_finset_insert a _ p (by
      simp [GaloisForLFunctions.mem_primesLE,p])]
  · have hP : GaloisForLFunctions.primesLE (n+1) = GaloisForLFunctions.primesLE n := by
      ext q
      simp only [GaloisForLFunctions.mem_primesLE]
      have hne : (q : ℕ) ≠ n+1 := by intro h; exact hn (h ▸ q.property)
      omega
    rw [hP]

def deningerDampedHalfDensityPrefix (a : ℝ) (n : ℕ) : DeningerHalfDensityL2 :=
  deningerStrongLogWeightedL2LM (1/2)
    (deningerDampedPrimeListSource a (GaloisForLFunctions.primesLE n).toList)

theorem deningerDampedHalfDensityPrefix_step (a : ℝ) (n : ℕ) :
    deningerDampedHalfDensityPrefix a (n+1) =
      if (n+1).Prime then
        deningerHalfDensityPairedPrime (Real.log ((n+1 : ℕ) : ℝ)) a (deningerDampedHalfDensityPrefix a n)
      else deningerDampedHalfDensityPrefix a n := by
  unfold deningerDampedHalfDensityPrefix
  rw [deningerDampedPrimePrefix_source_step]
  split_ifs <;> simp only [deningerStrongLogHalfDensity_paired]


private theorem deningerDampedHalfDensityPrefix_step_bounds {a : ℝ} (ha : 1/2 < a) (n : ℕ) :
    (1-deningerHalfDensityPrimeStepWeight a (n+1))^2 * ‖deningerDampedHalfDensityPrefix a n‖ ≤
      ‖deningerDampedHalfDensityPrefix a (n+1)‖ ∧
    ‖deningerDampedHalfDensityPrefix a (n+1)‖ ≤
      Real.exp (2*deningerHalfDensityPrimeStepWeight a (n+1)) * ‖deningerDampedHalfDensityPrefix a n‖ := by
  rw [deningerDampedHalfDensityPrefix_step]
  split_ifs with hn
  · let p : Nat.Primes := ⟨n+1,hn⟩
    have hw := deningerHalfDensityPrimeStepWeight_eq_exp a p
    change deningerHalfDensityPrimeStepWeight a (n+1) = _ at hw
    rw [hw]
    exact deningerHalfDensityPairedPrime_norm_bounds _ a
      (hw ▸ (deningerHalfDensityPrimeStepWeight_lt_one ha (n+1)).le) _
  · simp [deningerHalfDensityPrimeStepWeight,hn]

private theorem deningerDampedHalfDensityPrefix_step_increment {a : ℝ} (ha : 1/2 < a) (n : ℕ) :
    ‖deningerDampedHalfDensityPrefix a (n+1) - deningerDampedHalfDensityPrefix a n‖ ≤
      3*deningerHalfDensityPrimeStepWeight a (n+1)*‖deningerDampedHalfDensityPrefix a n‖ := by
  rw [deningerDampedHalfDensityPrefix_step]
  split_ifs with hn
  · let p : Nat.Primes := ⟨n+1,hn⟩
    have hw := deningerHalfDensityPrimeStepWeight_eq_exp a p
    change deningerHalfDensityPrimeStepWeight a (n+1) = _ at hw
    rw [hw]
    exact deningerHalfDensityPairedPrime_increment _ a
      (hw ▸ (deningerHalfDensityPrimeStepWeight_lt_one ha (n+1)).le) _
  · simp [deningerHalfDensityPrimeStepWeight,hn]

theorem deningerDampedHalfDensityPrefix_norm_le {a : ℝ} (ha : 1/2 < a) (n : ℕ) :
    ‖deningerDampedHalfDensityPrefix a n‖ ≤
      Real.exp (2*∑ k ∈ Finset.range n, deningerHalfDensityPrimeStepWeight a (k+1)) *
        ‖deningerDampedHalfDensityPrefix a 0‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      ‖deningerDampedHalfDensityPrefix a (n+1)‖ ≤
        Real.exp (2*deningerHalfDensityPrimeStepWeight a (n+1)) * ‖deningerDampedHalfDensityPrefix a n‖ :=
          (deningerDampedHalfDensityPrefix_step_bounds ha n).2
      _ ≤ Real.exp (2*deningerHalfDensityPrimeStepWeight a (n+1)) *
          (Real.exp (2*∑ k ∈ Finset.range n, deningerHalfDensityPrimeStepWeight a (k+1)) *
            ‖deningerDampedHalfDensityPrefix a 0‖) := by gcongr
      _ = _ := by rw [← mul_assoc, ← Real.exp_add, Finset.sum_range_succ]; congr 2; ring

def deningerDampedHalfDensityNormBound (a : ℝ) : ℝ :=
  Real.exp (2*∑' k : ℕ, deningerHalfDensityPrimeStepWeight a (k+1)) *
    ‖deningerDampedHalfDensityPrefix a 0‖

theorem deningerDampedHalfDensityPrefix_uniform_bound {a : ℝ} (ha : 1/2 < a) (n : ℕ) :
    ‖deningerDampedHalfDensityPrefix a n‖ ≤ deningerDampedHalfDensityNormBound a := by
  apply (deningerDampedHalfDensityPrefix_norm_le ha n).trans
  unfold deningerDampedHalfDensityNormBound
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact ((deningerHalfDensityPrimeStepWeight_summable ha).comp_injective
    (fun _ _ h => Nat.add_right_cancel h)).sum_le_tsum _
      (fun _ _ => deningerHalfDensityPrimeStepWeight_nonneg a _)

theorem deningerDampedHalfDensityPrefix_cauchy {a : ℝ} (ha : 1/2 < a) :
    CauchySeq (deningerDampedHalfDensityPrefix a) := by
  apply cauchySeq_of_dist_le_of_summable
    (fun n => 3*deningerHalfDensityPrimeStepWeight a (n+1)*deningerDampedHalfDensityNormBound a)
  · intro n
    rw [dist_comm,dist_eq_norm]
    apply (deningerDampedHalfDensityPrefix_step_increment ha n).trans
    exact mul_le_mul_of_nonneg_left (deningerDampedHalfDensityPrefix_uniform_bound ha n)
      (mul_nonneg (by norm_num) (deningerHalfDensityPrimeStepWeight_nonneg a _))
  · exact (((deningerHalfDensityPrimeStepWeight_summable ha).comp_injective
      (fun _ _ h => Nat.add_right_cancel h)).mul_left 3).mul_right _

def deningerDampedHalfDensityLimit (a : {a : ℝ // 1/2 < a}) : DeningerHalfDensityL2 :=
  Classical.choose (cauchySeq_tendsto_of_complete (deningerDampedHalfDensityPrefix_cauchy a.property))

theorem deningerDampedHalfDensityPrefix_tendsto (a : {a : ℝ // 1/2 < a}) :
    Tendsto (deningerDampedHalfDensityPrefix a.val) atTop (𝓝 (deningerDampedHalfDensityLimit a)) :=
  Classical.choose_spec (cauchySeq_tendsto_of_complete (deningerDampedHalfDensityPrefix_cauchy a.property))

theorem deningerDampedHalfDensityPrefix_error_bound (a : {a : ℝ // 1/2 < a}) (n : ℕ) :
    dist (deningerDampedHalfDensityPrefix a.val n) (deningerDampedHalfDensityLimit a) ≤
      ∑' k : ℕ, 3*deningerHalfDensityPrimeStepWeight a.val (n+k+1)*deningerDampedHalfDensityNormBound a.val := by
  apply dist_le_tsum_of_dist_le_of_tendsto
    (fun j => 3*deningerHalfDensityPrimeStepWeight a.val (j+1)*deningerDampedHalfDensityNormBound a.val)
  · intro j
    rw [dist_comm,dist_eq_norm]
    apply (deningerDampedHalfDensityPrefix_step_increment a.property j).trans
    exact mul_le_mul_of_nonneg_left (deningerDampedHalfDensityPrefix_uniform_bound a.property j)
      (mul_nonneg (by norm_num) (deningerHalfDensityPrimeStepWeight_nonneg a.val _))
  · exact (((deningerHalfDensityPrimeStepWeight_summable a.property).comp_injective
      (fun _ _ h => Nat.add_right_cancel h)).mul_left 3).mul_right _
  · exact deningerDampedHalfDensityPrefix_tendsto a

private theorem deningerDampedHalfDensityPrefix_norm_lower {a : ℝ} (ha : 1/2 < a) (n : ℕ) :
    (∏ k ∈ Finset.range n, (1-deningerHalfDensityPrimeStepWeight a (k+1)))^2 *
      ‖deningerDampedHalfDensityPrefix a 0‖ ≤ ‖deningerDampedHalfDensityPrefix a n‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, mul_pow]
    calc
      _ = (1-deningerHalfDensityPrimeStepWeight a (n+1))^2 *
          ((∏ k ∈ Finset.range n, (1-deningerHalfDensityPrimeStepWeight a (k+1)))^2 *
            ‖deningerDampedHalfDensityPrefix a 0‖) := by ring
      _ ≤ (1-deningerHalfDensityPrimeStepWeight a (n+1))^2 * ‖deningerDampedHalfDensityPrefix a n‖ :=
        mul_le_mul_of_nonneg_left ih (sq_nonneg _)
      _ ≤ _ := (deningerDampedHalfDensityPrefix_step_bounds ha n).1

def deningerDampedHalfDensityLowerFactor (a : ℝ) : ℝ :=
  Real.exp (∑' k : ℕ, Real.log (1-deningerHalfDensityPrimeStepWeight a (k+1)))

theorem deningerDampedHalfDensityLimit_norm_lower (a : {a : ℝ // 1/2 < a}) :
    deningerDampedHalfDensityLowerFactor a.val ^ 2 * ‖deningerDampedHalfDensityPrefix a.val 0‖ ≤
      ‖deningerDampedHalfDensityLimit a‖ := by
  have hs : Summable (fun k : ℕ => deningerHalfDensityPrimeStepWeight a.val (k+1)) :=
    (deningerHalfDensityPrimeStepWeight_summable a.property).comp_injective
      (fun _ _ h => Nat.add_right_cancel h)
  have hlog : Summable (fun k : ℕ => Real.log (1-deningerHalfDensityPrimeStepWeight a.val (k+1))) := by
    simpa only [Pi.neg_apply, sub_eq_add_neg] using Real.summable_log_one_add_of_summable hs.neg
  have hprod := Real.hasProd_of_hasSum_log
    (fun k : ℕ => sub_pos.mpr (deningerHalfDensityPrimeStepWeight_lt_one a.property (k+1))) hlog.hasSum
  exact le_of_tendsto_of_tendsto
    ((hprod.tendsto_prod_nat.pow 2).mul_const ‖deningerDampedHalfDensityPrefix a.val 0‖)
    (deningerDampedHalfDensityPrefix_tendsto a).norm
    (Filter.Eventually.of_forall (deningerDampedHalfDensityPrefix_norm_lower a.property))

theorem deningerDampedHalfDensityPrefix_zero (a : ℝ) :
    deningerDampedHalfDensityPrefix a 0 =
      deningerStrongLogWeightedL2LM (1/2) deningerMeyerReflectedLogGaussianSource := by
  have hP : GaloisForLFunctions.primesLE 0 = ∅ := by
    ext p
    simp only [GaloisForLFunctions.mem_primesLE, Finset.notMem_empty, iff_false, not_le]
    exact p.property.pos
  simp [deningerDampedHalfDensityPrefix,hP,deningerDampedPrimeListSource]

theorem deningerStrongLogHalfDensityGaussian_ne_zero :
    deningerStrongLogWeightedL2LM (1/2) deningerMeyerReflectedLogGaussianSource ≠ 0 := by
  intro h
  let f := deningerStrongLogWeightedSchwartzLM (1/2) deningerMeyerReflectedLogGaussianSource
  have hf : f.toLp 2 volume = 0 := h
  have hae : (f : ℝ → ℂ) =ᵐ[volume] 0 := by
    filter_upwards [f.coeFn_toLp (p:=2) (μ:=volume), Lp.coeFn_zero ℂ 2 volume] with t ht hzero
    rw [hf,hzero] at ht
    exact ht.symm
  have heq := MeasureTheory.Measure.eq_of_ae_eq hae f.continuous continuous_const
  have hzero := congrFun heq 0
  simp [f,deningerStrongLogWeightedSchwartzLM_apply,deningerMeyerReflectedLogGaussianSource_apply,
    GaloisForLFunctions.gaussReal] at hzero

theorem deningerDampedHalfDensityLimit_ne_zero (a : {a : ℝ // 1/2 < a}) :
    deningerDampedHalfDensityLimit a ≠ 0 := by
  have hg : 0 < ‖deningerDampedHalfDensityPrefix a.val 0‖ := by
    rw [deningerDampedHalfDensityPrefix_zero]
    exact norm_pos_iff.mpr deningerStrongLogHalfDensityGaussian_ne_zero
  have hl : 0 < deningerDampedHalfDensityLowerFactor a.val ^ 2 :=
    sq_pos_of_pos (Real.exp_pos _)
  exact norm_pos_iff.mp ((mul_pos hl hg).trans_le (deningerDampedHalfDensityLimit_norm_lower a))

/-- A concrete nonzero limit of the literal original-prime Gaussian sources, at damping one. -/
theorem deningerDampingOne_original_source_limit :
    ∃ h : DeningerHalfDensityL2, h ≠ 0 ∧ Tendsto
      (fun n => deningerStrongLogWeightedL2LM (1/2)
        (deningerDampedPrimeListSource 1 (GaloisForLFunctions.primesLE n).toList)) atTop (𝓝 h) := by
  let a : {a : ℝ // 1/2 < a} := ⟨1,by norm_num⟩
  refine ⟨deningerDampedHalfDensityLimit a, deningerDampedHalfDensityLimit_ne_zero a, ?_⟩
  change Tendsto (deningerDampedHalfDensityPrefix a.val) atTop (𝓝 (deningerDampedHalfDensityLimit a))
  exact deningerDampedHalfDensityPrefix_tendsto a


private theorem deningerHalfDensityTranslation_symm (L : ℝ) (f : DeningerHalfDensityL2) :
    (MellinL2.additiveTranslationUnitary L).symm f =
      MellinL2.additiveTranslationUnitary (-L) f := by
  change Lp.compMeasurePreserving (MellinL2.realTranslationEquiv L).symm
    (MellinL2.realTranslation_measurePreserving L).symm f =
      Lp.compMeasurePreserving (MellinL2.realTranslationEquiv (-L))
        (MellinL2.realTranslation_measurePreserving (-L)) f
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving f
      (MellinL2.realTranslation_measurePreserving L).symm,
    Lp.coeFn_compMeasurePreserving f (MellinL2.realTranslation_measurePreserving (-L))]
    with t hl hr
  rw [hl,hr]
  congr 1

theorem deningerHalfDensityPrimeMate_eq_adjoint (L a : ℝ) :
    deningerHalfDensityPrimeMate L a = (deningerHalfDensityPrimeFactor L a).adjoint := by
  have hU : ContinuousLinearMap.adjoint
      (MellinL2.additiveTranslationUnitary L).toLinearIsometry.toContinuousLinearMap =
        (MellinL2.additiveTranslationUnitary (-L)).toLinearIsometry.toContinuousLinearMap := by
    calc
      _ = ((MellinL2.additiveTranslationUnitary L).symm :
          DeningerHalfDensityL2 →L[ℂ] DeningerHalfDensityL2) :=
        (MellinL2.additiveTranslationUnitary L).adjoint_eq_symm
      _ = _ := by
        apply ContinuousLinearMap.ext
        intro f
        exact deningerHalfDensityTranslation_symm L f
  simp only [deningerHalfDensityPrimeMate,deningerHalfDensityPrimeFactor,
    map_sub,map_smulₛₗ,ContinuousLinearMap.adjoint_id,hU]
  have hr : (starRingEnd ℂ) (Real.exp (-(a+1/2)*L) : ℂ) =
      (Real.exp (-(a+1/2)*L) : ℂ) := Complex.conj_ofReal _
  rw [hr]

theorem deningerHalfDensityPairedPrime_energy (L a : ℝ) (f : DeningerHalfDensityL2) :
    (inner ℂ f (deningerHalfDensityPairedPrime L a f)).re =
      ‖deningerHalfDensityPrimeMate L a f‖^2 := by
  rw [ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right]
  have hD : (deningerHalfDensityPrimeMate L a).adjoint = deningerHalfDensityPrimeFactor L a := by
    rw [deningerHalfDensityPrimeMate_eq_adjoint,ContinuousLinearMap.adjoint_adjoint]
  rw [hD]
  rfl

theorem deningerHalfDensityPairedPrime_energy_nonneg (L a : ℝ) (f : DeningerHalfDensityL2) :
    0 ≤ (inner ℂ f (deningerHalfDensityPairedPrime L a f)).re := by
  rw [deningerHalfDensityPairedPrime_energy]
  exact sq_nonneg _

end RHTower
