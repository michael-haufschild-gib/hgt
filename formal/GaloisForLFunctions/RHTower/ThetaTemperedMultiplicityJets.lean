import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspSchwartzFourierXi
import GaloisForLFunctions.RHTower.XiHadamardFactorization
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaSourceUnconditional
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Actual Xi multiplicity kernel on finite Dirac jets

The real Xi symbol has a literal Schwartz Fourier representative, so its
multiplication operator on tempered distributions is actually admitted.
Signed Dirac-derivative pairings and polynomial theta probes identify the
kernel on all finite jets at a real point: exactly the jets strictly below
the actual analytic multiplicity, with dimension equal to that multiplicity.
The first excluded jet is nonzero. No RH or jet-vanishing premise is used.

Transport to the original unscaled source and the full supported-distribution
local/global converse are separate remaining obligations of the history card.
-/

open MeasureTheory Set Filter Topology
open scoped SchwartzMap FourierTransform
noncomputable section
namespace RHTower

private theorem thetaAnalyticIteratedDerivative (f : ℂ → ℂ)
    (hf : ∀ z, AnalyticAt ℂ f z) (n : ℕ) (z : ℂ) :
    AnalyticAt ℂ (iteratedDeriv n f) z := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using hf z
  | succ n ih => rw [iteratedDeriv_succ]; exact ih.deriv

private theorem thetaRealRestriction_iteratedDeriv (f : ℂ → ℂ)
    (hf : ∀ z, AnalyticAt ℂ f z) (n : ℕ) (t : ℝ) :
    iteratedDeriv n (fun u : ℝ => f (u : ℂ)) t = iteratedDeriv n f (t : ℂ) := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
      have heq : iteratedDeriv n (fun u : ℝ => f (u : ℂ)) =
          fun u : ℝ => iteratedDeriv n f (u : ℂ) := funext ih
      rw [iteratedDeriv_succ, iteratedDeriv_succ, heq]
      have hd := (thetaAnalyticIteratedDerivative f hf n (t : ℂ)).differentiableAt.hasDerivAt
      exact hd.comp_ofReal.deriv

def thetaXiRealSymbol (t : ℝ) : ℂ := XiC (t : ℂ)

def thetaXiSchwartzSymbol : 𝓢(ℝ, ℂ) := 𝓕 xiThetaSchwartzSource

theorem thetaXiSchwartzSymbol_apply (t : ℝ) :
    thetaXiSchwartzSymbol t = thetaXiRealSymbol t :=
  fourier_xiThetaSchwartzSource t

theorem thetaXiRealSymbol_eq_coeSchwartz :
    thetaXiRealSymbol = (thetaXiSchwartzSymbol : ℝ → ℂ) :=
  funext fun t => (thetaXiSchwartzSymbol_apply t).symm

theorem thetaXiRealSymbol_hasTemperateGrowth :
    Function.HasTemperateGrowth thetaXiRealSymbol := by
  rw [thetaXiRealSymbol_eq_coeSchwartz]
  exact thetaXiSchwartzSymbol.hasTemperateGrowth

theorem thetaXiComplexDerivative_analyticAt (n : ℕ) (z : ℂ) :
    AnalyticAt ℂ (iteratedDeriv n XiC) z :=
  thetaAnalyticIteratedDerivative XiC (fun z => XiC_analytic z (mem_univ z)) n z

theorem thetaXiRealSymbol_iteratedDeriv (n : ℕ) (t : ℝ) :
    iteratedDeriv n thetaXiRealSymbol t = iteratedDeriv n XiC (t : ℂ) :=
  thetaRealRestriction_iteratedDeriv XiC (fun z => XiC_analytic z (mem_univ z)) n t

def thetaRealXiMultiplicity (t : ℝ) : ℕ :=
  (analyticOrderAt XiC (t : ℂ)).toNat

theorem thetaRealXiMultiplicity_order (t : ℝ) :
    analyticOrderAt XiC (t : ℂ) = (thetaRealXiMultiplicity t : ℕ∞) := by
  exact (ENat.coe_toNat (XiC_order_ne_top (t : ℂ))).symm

theorem thetaXiComplexJet_vanish_below_multiplicity (t : ℝ) {r : ℕ}
    (hr : r < thetaRealXiMultiplicity t) : iteratedDeriv r XiC (t : ℂ) = 0 :=
  ((analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero
    (XiC_analytic (t : ℂ) (mem_univ _))).mp (thetaRealXiMultiplicity_order t)).1 r hr

theorem thetaXiComplexJet_ne_zero_at_multiplicity (t : ℝ) :
    iteratedDeriv (thetaRealXiMultiplicity t) XiC (t : ℂ) ≠ 0 :=
  ((analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero
    (XiC_analytic (t : ℂ) (mem_univ _))).mp (thetaRealXiMultiplicity_order t)).2

theorem thetaRealXiMultiplicity_pos_iff (t : ℝ) :
    0 < thetaRealXiMultiplicity t ↔ XiC (t : ℂ) = 0 := by
  constructor
  · intro hm
    simpa only [iteratedDeriv_zero] using thetaXiComplexJet_vanish_below_multiplicity t hm
  · intro hzero
    by_contra hpos
    have hm : thetaRealXiMultiplicity t = 0 := Nat.eq_zero_of_not_pos hpos
    have hne := thetaXiComplexJet_ne_zero_at_multiplicity t
    rw [hm, iteratedDeriv_zero, hzero] at hne
    exact hne rfl

def thetaRealDiracJet (t : ℝ) (r : ℕ) : 𝓢'(ℝ, ℂ) :=
  (TemperedDistribution.derivCLM ℂ)^[r] (TemperedDistribution.delta t)

theorem thetaRealDiracJet_apply (t : ℝ) (r : ℕ) (φ : 𝓢(ℝ, ℂ)) :
    thetaRealDiracJet t r φ = (-1 : ℂ) ^ r * iteratedDeriv r (φ : ℝ → ℂ) t := by
  induction r generalizing φ with
  | zero => simp [thetaRealDiracJet, iteratedDeriv_zero]
  | succ r ih =>
      rw [thetaRealDiracJet, Function.iterate_succ_apply',
        TemperedDistribution.derivCLM_apply_apply, map_neg]
      change -thetaRealDiracJet t r (SchwartzMap.derivCLM ℂ ℂ φ) = _
      rw [ih]
      change -((-1 : ℂ) ^ r * iteratedDeriv r (deriv (φ : ℝ → ℂ)) t) = _
      rw [iteratedDeriv_succ', pow_succ]
      ring

def thetaXiTemperedMultiplier : 𝓢'(ℝ, ℂ) →L[ℂ] 𝓢'(ℝ, ℂ) :=
  TemperedDistribution.smulLeftCLM ℂ thetaXiRealSymbol

theorem thetaXiTemperedMultiplier_jet_apply (t : ℝ) (r : ℕ) (φ : 𝓢(ℝ, ℂ)) :
    thetaXiTemperedMultiplier (thetaRealDiracJet t r) φ =
      (-1 : ℂ) ^ r * ∑ j ∈ Finset.range (r + 1),
        (r.choose j : ℂ) * iteratedDeriv j XiC (t : ℂ) *
          iteratedDeriv (r - j) (φ : ℝ → ℂ) t := by
  have heq : (SchwartzMap.smulLeftCLM ℂ thetaXiRealSymbol φ : ℝ → ℂ) =
      thetaXiRealSymbol * (φ : ℝ → ℂ) := by
    funext x
    rw [SchwartzMap.smulLeftCLM_apply_apply thetaXiRealSymbol_hasTemperateGrowth]
    rfl
  have hs : ContDiffAt ℝ r thetaXiRealSymbol t := by
    rw [thetaXiRealSymbol_eq_coeSchwartz]
    exact (thetaXiSchwartzSymbol.smooth r).contDiffAt
  change TemperedDistribution.smulLeftCLM ℂ thetaXiRealSymbol
    (thetaRealDiracJet t r) φ = _
  rw [TemperedDistribution.smulLeftCLM_apply_apply, thetaRealDiracJet_apply, heq,
    iteratedDeriv_mul hs (φ.smooth r).contDiffAt]
  simp_rw [thetaXiRealSymbol_iteratedDeriv]

theorem thetaXiTemperedMultiplier_jet_eq_zero_of_lt_multiplicity (t : ℝ) {r : ℕ}
    (hr : r < thetaRealXiMultiplicity t) :
    thetaXiTemperedMultiplier (thetaRealDiracJet t r) = 0 := by
  ext φ
  rw [thetaXiTemperedMultiplier_jet_apply]
  have hsum : (∑ j ∈ Finset.range (r + 1),
      (r.choose j : ℂ) * iteratedDeriv j XiC (t : ℂ) *
        iteratedDeriv (r - j) (φ : ℝ → ℂ) t) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hjm : j < thetaRealXiMultiplicity t := by
      have := Finset.mem_range.mp hj
      omega
    rw [thetaXiComplexJet_vanish_below_multiplicity t hjm, mul_zero, zero_mul]
  rw [hsum, mul_zero]
  rfl

theorem thetaXiTemperedMultiplier_jet_at_multiplicity_ne_zero (t : ℝ) :
    thetaXiTemperedMultiplier (thetaRealDiracJet t (thetaRealXiMultiplicity t)) ≠ 0 := by
  let m := thetaRealXiMultiplicity t
  have hsum : (∑ j ∈ Finset.range (m + 1),
      (m.choose j : ℂ) * iteratedDeriv j XiC (t : ℂ) *
        iteratedDeriv (m - j) (thetaCuspSchwartz : ℝ → ℂ) t) =
      iteratedDeriv m XiC (t : ℂ) * thetaCuspSchwartz t := by
    rw [Finset.sum_eq_single m]
    · simp only [Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self, iteratedDeriv_zero]
    · intro j hj hjne
      have hjm : j < thetaRealXiMultiplicity t := by
        have := Finset.mem_range.mp hj
        dsimp [m] at *
        omega
      rw [thetaXiComplexJet_vanish_below_multiplicity t hjm, mul_zero, zero_mul]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr (Nat.lt_succ_self m))).elim
  have hφ : thetaCuspSchwartz t ≠ 0 := by
    rw [thetaCuspSchwartz_apply]
    exact_mod_cast (HedenmalmThetaSource.thetaCuspFullSource_pos t).ne'
  intro hzero
  have hv := congrArg (fun T : 𝓢'(ℝ, ℂ) => T thetaCuspSchwartz) hzero
  rw [thetaXiTemperedMultiplier_jet_apply, hsum] at hv
  exact (mul_ne_zero (pow_ne_zero m (by norm_num : (-1 : ℂ) ≠ 0))
    (mul_ne_zero (thetaXiComplexJet_ne_zero_at_multiplicity t) hφ)) hv

def thetaRealCenteredPower (t : ℝ) (r : ℕ) (x : ℝ) : ℂ :=
  ((x : ℂ) - (t : ℂ)) ^ r

theorem thetaRealCenteredPower_hasTemperateGrowth (t : ℝ) (r : ℕ) :
    Function.HasTemperateGrowth (thetaRealCenteredPower t r) := by
  unfold thetaRealCenteredPower
  fun_prop

theorem thetaRealCenteredPower_iteratedDeriv (t : ℝ) (r j : ℕ) :
    iteratedDeriv j (thetaRealCenteredPower t r) t =
      if j = r then (r.factorial : ℂ) else 0 := by
  unfold thetaRealCenteredPower
  rw [thetaRealRestriction_iteratedDeriv (fun z : ℂ => (z - (t : ℂ)) ^ r)
    (fun z => by fun_prop) j t,
    iteratedDeriv_comp_sub_const (f := fun z : ℂ => z ^ r) (s := (t : ℂ)) (n := j)]
  change iteratedDeriv j (fun z : ℂ => z ^ r) ((t : ℂ) - (t : ℂ)) = _
  rw [sub_self, iteratedDeriv_fun_pow_zero]
  split_ifs <;> simp

def thetaRealDiracJetProbe (t : ℝ) (r : ℕ) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (thetaRealCenteredPower t r) thetaCuspSchwartz

theorem thetaRealDiracJetProbe_coe (t : ℝ) (r : ℕ) :
    (thetaRealDiracJetProbe t r : ℝ → ℂ) =
      thetaRealCenteredPower t r * (thetaCuspSchwartz : ℝ → ℂ) := by
  funext x
  rw [thetaRealDiracJetProbe,
    SchwartzMap.smulLeftCLM_apply_apply (thetaRealCenteredPower_hasTemperateGrowth t r)]
  rfl

theorem thetaRealDiracJetProbe_iteratedDeriv (t : ℝ) (r : ℕ) {j : ℕ} (hj : j ≤ r) :
    iteratedDeriv j (thetaRealDiracJetProbe t r : ℝ → ℂ) t =
      if j = r then (r.factorial : ℂ) * thetaCuspSchwartz t else 0 := by
  have hp : ContDiff ℝ j (thetaRealCenteredPower t r) := by
    unfold thetaRealCenteredPower
    exact (Complex.ofRealCLM.contDiff.sub contDiff_const).pow r
  rw [thetaRealDiracJetProbe_coe,
    iteratedDeriv_mul hp.contDiffAt (thetaCuspSchwartz.smooth j).contDiffAt]
  by_cases heq : j = r
  · subst j
    rw [if_pos rfl, Finset.sum_eq_single r]
    · simp only [Nat.choose_self, Nat.cast_one, one_mul,
        thetaRealCenteredPower_iteratedDeriv, ite_true, Nat.sub_self, iteratedDeriv_zero]
    · intro i hi hne
      rw [thetaRealCenteredPower_iteratedDeriv, if_neg hne, mul_zero, zero_mul]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr (Nat.lt_succ_self r))).elim
  · rw [if_neg heq]
    apply Finset.sum_eq_zero
    intro i hi
    have hne : i ≠ r := by
      have := Finset.mem_range.mp hi
      omega
    rw [thetaRealCenteredPower_iteratedDeriv, if_neg hne, mul_zero, zero_mul]

theorem thetaRealDiracJet_selfProbe_ne_zero (t : ℝ) (r : ℕ) :
    thetaRealDiracJet t r (thetaRealDiracJetProbe t r) ≠ 0 := by
  rw [thetaRealDiracJet_apply, thetaRealDiracJetProbe_iteratedDeriv t r le_rfl, if_pos rfl]
  have hφ : thetaCuspSchwartz t ≠ 0 := by
    rw [thetaCuspSchwartz_apply]
    exact_mod_cast (HedenmalmThetaSource.thetaCuspFullSource_pos t).ne'
  exact mul_ne_zero (pow_ne_zero r (by norm_num))
    (mul_ne_zero (Nat.cast_ne_zero.mpr r.factorial_ne_zero) hφ)

theorem thetaRealDiracJet_ne_zero (t : ℝ) (r : ℕ) : thetaRealDiracJet t r ≠ 0 := by
  intro hzero
  apply thetaRealDiracJet_selfProbe_ne_zero t r
  rw [hzero]
  rfl

private def thetaDiracJetProbeEvaluation (t : ℝ) (r : ℕ) : 𝓢'(ℝ, ℂ) →ₗ[ℂ] ℂ where
  toFun T := T (thetaRealDiracJetProbe t r)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem thetaRealDiracJet_fin_linearIndependent (t : ℝ) (N : ℕ) :
    LinearIndependent ℂ (fun r : Fin N => thetaRealDiracJet t r) := by
  induction N with
  | zero => exact linearIndependent_empty_type
  | succ N ih =>
      apply linearIndependent_finSucc'.mpr
      constructor
      · exact ih
      · let v : Fin (N + 1) → 𝓢'(ℝ, ℂ) := fun r => thetaRealDiracJet t r
        have hker : Submodule.span ℂ (Set.range (Fin.init v)) ≤
            (thetaDiracJetProbeEvaluation t N).ker := by
          apply Submodule.span_le.mpr
          rintro _ ⟨r, rfl⟩
          change thetaRealDiracJet t (r : ℕ) (thetaRealDiracJetProbe t N) = 0
          rw [thetaRealDiracJet_apply, thetaRealDiracJetProbe_iteratedDeriv t N
            (le_of_lt r.isLt), if_neg (ne_of_lt r.isLt), mul_zero]
        intro hmem
        have hz := hker hmem
        change thetaRealDiracJet t N (thetaRealDiracJetProbe t N) = 0 at hz
        exact thetaRealDiracJet_selfProbe_ne_zero t N hz

def thetaXiTemperedLowerJetSpan (t : ℝ) : Submodule ℂ (𝓢'(ℝ, ℂ)) :=
  Submodule.span ℂ (Set.range (fun r : Fin (thetaRealXiMultiplicity t) => thetaRealDiracJet t r))

theorem thetaXiTemperedLowerJetSpan_le_ker (t : ℝ) :
    thetaXiTemperedLowerJetSpan t ≤ thetaXiTemperedMultiplier.ker := by
  apply Submodule.span_le.mpr
  rintro _ ⟨r, rfl⟩
  exact thetaXiTemperedMultiplier_jet_eq_zero_of_lt_multiplicity t r.isLt

theorem thetaXiTemperedLowerJetSpan_finrank (t : ℝ) :
    Module.finrank ℂ (thetaXiTemperedLowerJetSpan t) = thetaRealXiMultiplicity t := by
  change Module.finrank ℂ (Submodule.span ℂ (Set.range
    (fun r : Fin (thetaRealXiMultiplicity t) => thetaRealDiracJet t r))) = _
  rw [finrank_span_eq_card (thetaRealDiracJet_fin_linearIndependent t (thetaRealXiMultiplicity t))]
  exact Fintype.card_fin _

theorem thetaXiTemperedMultiplier_probe_vanish_below (t : ℝ) (q : ℕ) {r : ℕ}
    (hr : r < thetaRealXiMultiplicity t + q) :
    thetaXiTemperedMultiplier (thetaRealDiracJet t r) (thetaRealDiracJetProbe t q) = 0 := by
  rw [thetaXiTemperedMultiplier_jet_apply]
  have hsum : (∑ j ∈ Finset.range (r + 1),
      (r.choose j : ℂ) * iteratedDeriv j XiC (t : ℂ) *
        iteratedDeriv (r - j) (thetaRealDiracJetProbe t q : ℝ → ℂ) t) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    by_cases hjm : j < thetaRealXiMultiplicity t
    · rw [thetaXiComplexJet_vanish_below_multiplicity t hjm, mul_zero, zero_mul]
    · have hq : r - j < q := by
        have := Finset.mem_range.mp hj
        omega
      rw [thetaRealDiracJetProbe_iteratedDeriv t q (le_of_lt hq),
        if_neg (ne_of_lt hq), mul_zero]
  rw [hsum, mul_zero]

theorem thetaXiTemperedMultiplier_probe_at_order (t : ℝ) (q : ℕ) :
    thetaXiTemperedMultiplier (thetaRealDiracJet t (thetaRealXiMultiplicity t + q))
        (thetaRealDiracJetProbe t q) =
      (-1 : ℂ) ^ (thetaRealXiMultiplicity t + q) *
        (((thetaRealXiMultiplicity t + q).choose (thetaRealXiMultiplicity t) : ℂ) *
          iteratedDeriv (thetaRealXiMultiplicity t) XiC (t : ℂ) *
            ((q.factorial : ℂ) * thetaCuspSchwartz t)) := by
  rw [thetaXiTemperedMultiplier_jet_apply]
  congr 1
  let m := thetaRealXiMultiplicity t
  change (∑ j ∈ Finset.range (m + q + 1),
      ((m + q).choose j : ℂ) * iteratedDeriv j XiC (t : ℂ) *
        iteratedDeriv (m + q - j) (thetaRealDiracJetProbe t q : ℝ → ℂ) t) = _
  rw [Finset.sum_eq_single m]
  · have hd : m + q - m = q := by omega
    rw [hd, thetaRealDiracJetProbe_iteratedDeriv t q le_rfl, if_pos rfl]
  · intro j hj hjne
    by_cases hjm : j < thetaRealXiMultiplicity t
    · rw [thetaXiComplexJet_vanish_below_multiplicity t hjm, mul_zero, zero_mul]
    · have hq : m + q - j < q := by
        have := Finset.mem_range.mp hj
        dsimp [m] at *
        omega
      rw [thetaRealDiracJetProbe_iteratedDeriv t q (le_of_lt hq),
        if_neg (ne_of_lt hq), mul_zero]
  · intro hnot
    apply hnot.elim
    apply Finset.mem_range.mpr
    omega

theorem thetaXiTemperedMultiplier_probe_at_order_ne_zero (t : ℝ) (q : ℕ) :
    thetaXiTemperedMultiplier (thetaRealDiracJet t (thetaRealXiMultiplicity t + q))
      (thetaRealDiracJetProbe t q) ≠ 0 := by
  rw [thetaXiTemperedMultiplier_probe_at_order]
  have hc : (((thetaRealXiMultiplicity t + q).choose (thetaRealXiMultiplicity t) : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ne_of_gt (Nat.choose_pos (by omega)))
  have hφ : thetaCuspSchwartz t ≠ 0 := by
    rw [thetaCuspSchwartz_apply]
    exact_mod_cast (HedenmalmThetaSource.thetaCuspFullSource_pos t).ne'
  exact mul_ne_zero (pow_ne_zero _ (by norm_num))
    (mul_ne_zero (mul_ne_zero hc (thetaXiComplexJet_ne_zero_at_multiplicity t))
      (mul_ne_zero (Nat.cast_ne_zero.mpr q.factorial_ne_zero) hφ))

def thetaRealDiracJetSum (t : ℝ) (N : ℕ) (a : ℕ → ℂ) : 𝓢'(ℝ, ℂ) :=
  ∑ r ∈ Finset.range N, a r • thetaRealDiracJet t r

theorem thetaRealDiracJetSum_ker_iff (t : ℝ) (N : ℕ) (a : ℕ → ℂ) :
    thetaXiTemperedMultiplier (thetaRealDiracJetSum t N a) = 0 ↔
      ∀ r < N, thetaRealXiMultiplicity t ≤ r → a r = 0 := by
  constructor
  · induction N with
    | zero => intro h r hr; omega
    | succ N ih =>
        intro hzero
        by_cases hmN : thetaRealXiMultiplicity t ≤ N
        · let q := N - thetaRealXiMultiplicity t
          have hN : thetaRealXiMultiplicity t + q = N := by dsimp [q]; omega
          let L : 𝓢'(ℝ, ℂ) →ₗ[ℂ] ℂ :=
            (thetaDiracJetProbeEvaluation t q).comp thetaXiTemperedMultiplier.toLinearMap
          have he : L (thetaRealDiracJetSum t (N + 1) a) = 0 := by
            change thetaXiTemperedMultiplier (thetaRealDiracJetSum t (N + 1) a)
              (thetaRealDiracJetProbe t q) = 0
            rw [hzero]
            rfl
          rw [thetaRealDiracJetSum, map_sum] at he
          simp_rw [map_smul] at he
          change (∑ r ∈ Finset.range (N + 1), a r *
            thetaXiTemperedMultiplier (thetaRealDiracJet t r) (thetaRealDiracJetProbe t q)) = 0 at he
          have hl : (∑ r ∈ Finset.range N, a r *
              thetaXiTemperedMultiplier (thetaRealDiracJet t r) (thetaRealDiracJetProbe t q)) = 0 := by
            apply Finset.sum_eq_zero
            intro r hr
            rw [thetaXiTemperedMultiplier_probe_vanish_below t q
              (by have := Finset.mem_range.mp hr; omega), mul_zero]
          rw [Finset.sum_range_succ, hl, zero_add] at he
          have hp : thetaXiTemperedMultiplier (thetaRealDiracJet t N)
              (thetaRealDiracJetProbe t q) ≠ 0 := by
            rw [← hN]
            exact thetaXiTemperedMultiplier_probe_at_order_ne_zero t q
          have haN : a N = 0 := (mul_eq_zero.mp he).resolve_right hp
          have hprev : thetaXiTemperedMultiplier (thetaRealDiracJetSum t N a) = 0 := by
            have hh := hzero
            rw [thetaRealDiracJetSum, Finset.sum_range_succ, map_add, map_smul, haN] at hh
            rw [zero_smul ℂ (thetaXiTemperedMultiplier (thetaRealDiracJet t N)), add_zero] at hh
            exact hh
          intro r hr hmr
          by_cases hrN : r < N
          · exact ih hprev r hrN hmr
          · have hrEq : r = N := by omega
            simpa only [hrEq] using haN
        · intro r hr hmr
          omega
  · intro ha
    rw [thetaRealDiracJetSum, map_sum]
    apply Finset.sum_eq_zero
    intro r hr
    rw [map_smul]
    by_cases hrm : r < thetaRealXiMultiplicity t
    · rw [thetaXiTemperedMultiplier_jet_eq_zero_of_lt_multiplicity t hrm, smul_zero]
    · rw [ha r (Finset.mem_range.mp hr) (by omega)]
      exact zero_smul ℂ (thetaXiTemperedMultiplier (thetaRealDiracJet t r))

def thetaRealDiracJetSpan (t : ℝ) : Submodule ℂ (𝓢'(ℝ, ℂ)) :=
  Submodule.span ℂ (Set.range (thetaRealDiracJet t))

theorem thetaXiTemperedLowerJetSpan_le_diracJetSpan (t : ℝ) :
    thetaXiTemperedLowerJetSpan t ≤ thetaRealDiracJetSpan t := by
  apply Submodule.span_le.mpr
  rintro _ ⟨r, rfl⟩
  exact Submodule.subset_span (Set.mem_range.mpr ⟨(r : ℕ), rfl⟩)

theorem thetaXiTemperedMultiplier_ker_inter_diracJetSpan (t : ℝ) :
    thetaRealDiracJetSpan t ⊓ thetaXiTemperedMultiplier.ker = thetaXiTemperedLowerJetSpan t := by
  classical
  apply le_antisymm
  · intro T hT
    rcases hT with ⟨hspan, hker⟩
    obtain ⟨a, ha⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hspan
    let N := a.support.sup id + 1
    have hsup : a.support ⊆ Finset.range N := by
      intro r hr
      have hs : r ≤ a.support.sup id := Finset.le_sup (f := id) hr
      apply Finset.mem_range.mpr
      dsimp [N]
      omega
    have hsum : thetaRealDiracJetSum t N a = T := by
      have hh := a.sum_of_support_subset hsup
        (fun r c => c • thetaRealDiracJet t r) (fun r hr => zero_smul ℂ (thetaRealDiracJet t r))
      exact hh.symm.trans ha
    have hz : thetaXiTemperedMultiplier (thetaRealDiracJetSum t N a) = 0 := by
      rw [hsum]
      exact hker
    have hcoeff := (thetaRealDiracJetSum_ker_iff t N a).mp hz
    rw [← hsum, thetaRealDiracJetSum]
    apply Submodule.sum_mem
    intro r hr
    by_cases hrm : r < thetaRealXiMultiplicity t
    · apply Submodule.smul_mem
      exact Submodule.subset_span (Set.mem_range.mpr ⟨⟨r, hrm⟩, rfl⟩)
    · rw [hcoeff r (Finset.mem_range.mp hr) (by omega)]
      rw [zero_smul ℂ (thetaRealDiracJet t r)]
      exact Submodule.zero_mem _
  · intro T hT
    exact ⟨thetaXiTemperedLowerJetSpan_le_diracJetSpan t hT,
      thetaXiTemperedLowerJetSpan_le_ker t hT⟩

end RHTower
