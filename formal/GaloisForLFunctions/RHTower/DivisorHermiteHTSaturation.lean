import GaloisForLFunctions.RHTower.DeBrangesHTGaugeSaturation
import GaloisForLFunctions.HTGeometry.AlmostDisjointIsodivisorialFrame
import GaloisForLFunctions.HTGeometry.MeromorphicFractionRealization
import GaloisForLFunctions.HTGeometry.MeroExponentialGauge
import GaloisForLFunctions.HTGeometry.AllJetLevelSet

/-!
# Divisor--Hermite saturation by hypertranscendental functions

Closed discrete Hermite passports are imposed on a hypertranscendental entire exponent.  Its
zero-free exponential pencil preserves every local meromorphic divisor and every prescribed
finite jet.  Differential-field cancellation removes at most one real parameter, leaving an
injective continuum of hypertranscendental global meromorphic representatives.
-/

open Set Complex Filter Topology
open scoped Differential UnivMeroFieldInstances

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry
open Bottcher

noncomputable section

def divisorHermiteGaugePhase (Q : ℂ → ℂ) (c : ℝ) : ℂ → ℂ :=
  htPassportGauge Q c

theorem analyticOnNhd_divisorHermiteGaugePhase {Q : ℂ → ℂ}
    (hQ : AnalyticOnNhd ℂ Q Set.univ) (c : ℝ) :
    AnalyticOnNhd ℂ (divisorHermiteGaugePhase Q c) Set.univ :=
  analyticOnNhd_htPassportGauge hQ c

theorem divisorHermiteGaugePhase_ne_zero (Q : ℂ → ℂ) (c : ℝ) (z : ℂ) :
    divisorHermiteGaugePhase Q c z ≠ 0 :=
  Complex.exp_ne_zero _

def divisorHermiteGaugePhaseMero (Q : ℂ → ℂ)
    (hQ : AnalyticOnNhd ℂ Q Set.univ) (c : ℝ) : meroField Set.univ :=
  analyticMeroElement (divisorHermiteGaugePhase Q c)
    (analyticOnNhd_divisorHermiteGaugePhase hQ c)

theorem divisorHermiteGaugePhaseMero_ne_zero {Q : ℂ → ℂ}
    (hQ : AnalyticOnNhd ℂ Q Set.univ) (c : ℝ) :
    divisorHermiteGaugePhaseMero Q hQ c ≠ 0 := by
  unfold divisorHermiteGaugePhaseMero divisorHermiteGaugePhase htPassportGauge
  exact analyticMeroElement_exp_ne_zero (fun z => (c : ℂ) * Q z)
    (analyticOnNhd_const.mul hQ)

theorem divisorHermiteGaugePhaseMero_add {Q : ℂ → ℂ}
    (hQ : AnalyticOnNhd ℂ Q Set.univ) (c d : ℝ) :
    divisorHermiteGaugePhaseMero Q hQ (c + d) =
      divisorHermiteGaugePhaseMero Q hQ c * divisorHermiteGaugePhaseMero Q hQ d := by
  unfold divisorHermiteGaugePhaseMero
  rw [← analyticMeroElement_mul]
  apply analyticMeroElement_congr
  funext z
  simp [divisorHermiteGaugePhase, htPassportGauge, add_mul, Complex.exp_add]

@[simp] theorem divisorHermiteGaugePhaseMero_zero {Q : ℂ → ℂ}
    (hQ : AnalyticOnNhd ℂ Q Set.univ) :
    divisorHermiteGaugePhaseMero Q hQ 0 = 1 := by
  unfold divisorHermiteGaugePhaseMero
  calc
    analyticMeroElement (divisorHermiteGaugePhase Q 0)
        (analyticOnNhd_divisorHermiteGaugePhase hQ 0) =
        analyticMeroElement (fun _ : ℂ => 1) analyticOnNhd_const := by
      apply analyticMeroElement_congr
      funext z
      simp [divisorHermiteGaugePhase, htPassportGauge]
    _ = 1 := by rw [analyticMeroElement_const]; simp

theorem divisorHermiteGaugePhaseMero_div {Q : ℂ → ℂ}
    (hQ : AnalyticOnNhd ℂ Q Set.univ) (c d : ℝ) :
    divisorHermiteGaugePhaseMero Q hQ c / divisorHermiteGaugePhaseMero Q hQ d =
      divisorHermiteGaugePhaseMero Q hQ (c - d) := by
  apply (div_eq_iff (divisorHermiteGaugePhaseMero_ne_zero hQ d)).2
  rw [← divisorHermiteGaugePhaseMero_add hQ, sub_add_cancel]

theorem hypertranscendentalOver_divisorHermiteGaugePhaseMero
    {Q : ℂ → ℂ} (hQ : AnalyticOnNhd ℂ Q Set.univ)
    (hQHT : Hypertranscendental Q) {c : ℝ} (hc : c ≠ 0) :
    HypertranscendentalOver (RatFunc ℂ) (divisorHermiteGaugePhaseMero Q hQ c) := by
  intro hDA
  apply hypertranscendental_htPassportGauge hQ hQHT hc
  exact differentiallyAlgebraic_of_differentialAlgebraicOver_analyticMeroElement
    (analyticOnNhd_divisorHermiteGaugePhase hQ c) hDA

def divisorHermiteGaugeElement (G : meroField Set.univ) (Q : ℂ → ℂ)
    (hQ : AnalyticOnNhd ℂ Q Set.univ) (c : ℝ) : meroField Set.univ :=
  G * divisorHermiteGaugePhaseMero Q hQ c

def divisorHermiteGaugeRepresentative (g Q : ℂ → ℂ) (c : ℝ) (z : ℂ) : ℂ :=
  g z * divisorHermiteGaugePhase Q c z

@[simp] theorem divisorHermiteGaugeElement_zero (G : meroField Set.univ) (Q : ℂ → ℂ)
    (hQ : AnalyticOnNhd ℂ Q Set.univ) :
    divisorHermiteGaugeElement G Q hQ 0 = G := by
  simp [divisorHermiteGaugeElement]

@[simp] theorem divisorHermiteGaugeRepresentative_zero (g Q : ℂ → ℂ) :
    divisorHermiteGaugeRepresentative g Q 0 = g := by
  funext z
  simp [divisorHermiteGaugeRepresentative, divisorHermiteGaugePhase, htPassportGauge]

theorem differentialAlgebraicOver_divisorHermiteGaugeElement_unique
    {G : meroField Set.univ} (hGne : G ≠ 0)
    {Q : ℂ → ℂ} (hQ : AnalyticOnNhd ℂ Q Set.univ)
    (hQHT : Hypertranscendental Q) {c d : ℝ}
    (hc : DifferentialAlgebraicOver (RatFunc ℂ) (divisorHermiteGaugeElement G Q hQ c))
    (hd : DifferentialAlgebraicOver (RatFunc ℂ) (divisorHermiteGaugeElement G Q hQ d)) :
    c = d := by
  by_contra hcd
  have hdiff : c - d ≠ 0 := sub_ne_zero.mpr hcd
  have hquot : DifferentialAlgebraicOver (RatFunc ℂ)
      (divisorHermiteGaugeElement G Q hQ c / divisorHermiteGaugeElement G Q hQ d) :=
    differentialAlgebraicOver_div hc hd
  have heq : divisorHermiteGaugeElement G Q hQ c /
      divisorHermiteGaugeElement G Q hQ d = divisorHermiteGaugePhaseMero Q hQ (c - d) := by
    unfold divisorHermiteGaugeElement
    rw [mul_div_mul_left _ _ hGne, divisorHermiteGaugePhaseMero_div]
  rw [heq] at hquot
  exact hypertranscendentalOver_divisorHermiteGaugePhaseMero hQ hQHT hdiff hquot

theorem divisorHermiteGaugeElement_parameterSet_subsingleton
    {G : meroField Set.univ} (hGne : G ≠ 0)
    {Q : ℂ → ℂ} (hQ : AnalyticOnNhd ℂ Q Set.univ)
    (hQHT : Hypertranscendental Q) :
    {c : ℝ | DifferentialAlgebraicOver (RatFunc ℂ)
      (divisorHermiteGaugeElement G Q hQ c)}.Subsingleton := by
  intro c hc d hd
  exact differentialAlgebraicOver_divisorHermiteGaugeElement_unique hGne hQ hQHT hc hd

theorem hypertranscendentalOver_divisorHermiteGaugeElement_of_base_DA
    {G : meroField Set.univ} (hGne : G ≠ 0)
    (hGDA : DifferentialAlgebraicOver (RatFunc ℂ) G)
    {Q : ℂ → ℂ} (hQ : AnalyticOnNhd ℂ Q Set.univ)
    (hQHT : Hypertranscendental Q) {c : ℝ} (hc : c ≠ 0) :
    HypertranscendentalOver (RatFunc ℂ) (divisorHermiteGaugeElement G Q hQ c) := by
  intro hcDA
  have hzeroDA : DifferentialAlgebraicOver (RatFunc ℂ)
      (divisorHermiteGaugeElement G Q hQ 0) := by simpa using hGDA
  exact hc (differentialAlgebraicOver_divisorHermiteGaugeElement_unique
    hGne hQ hQHT hcDA hzeroDA)

theorem injective_divisorHermiteGaugePhaseMero {Q : ℂ → ℂ}
    (hQ : AnalyticOnNhd ℂ Q Set.univ) (hQHT : Hypertranscendental Q) :
    Function.Injective (divisorHermiteGaugePhaseMero Q hQ) := by
  intro c d hcd
  apply injective_htPassportGauge hQ hQHT
  funext z
  change analyticMeroElement (divisorHermiteGaugePhase Q c)
      (analyticOnNhd_divisorHermiteGaugePhase hQ c) =
    analyticMeroElement (divisorHermiteGaugePhase Q d)
      (analyticOnNhd_divisorHermiteGaugePhase hQ d) at hcd
  have hzero : analyticMeroElement
      (fun w => divisorHermiteGaugePhase Q c w - divisorHermiteGaugePhase Q d w)
      ((analyticOnNhd_divisorHermiteGaugePhase hQ c).sub
        (analyticOnNhd_divisorHermiteGaugePhase hQ d)) = 0 := by
    rw [analyticMeroElement_sub
      (analyticOnNhd_divisorHermiteGaugePhase hQ c)
      (analyticOnNhd_divisorHermiteGaugePhase hQ d)]
    exact sub_eq_zero.mpr hcd
  exact sub_eq_zero.mp ((analyticMeroElement_eq_zero_iff _).mp hzero z (Set.mem_univ z))

theorem injective_divisorHermiteGaugeElement
    {G : meroField Set.univ} (hGne : G ≠ 0)
    {Q : ℂ → ℂ} (hQ : AnalyticOnNhd ℂ Q Set.univ)
    (hQHT : Hypertranscendental Q) :
    Function.Injective (divisorHermiteGaugeElement G Q hQ) := by
  intro c d hcd
  apply injective_divisorHermiteGaugePhaseMero hQ hQHT
  exact mul_left_cancel₀ hGne hcd

theorem meromorphicOn_divisorHermiteGaugeRepresentative
    {g Q : ℂ → ℂ} (hg : MeromorphicOn g Set.univ)
    (hQ : AnalyticOnNhd ℂ Q Set.univ) (c : ℝ) :
    MeromorphicOn (divisorHermiteGaugeRepresentative g Q c) Set.univ :=
  hg.mul (analyticOnNhd_divisorHermiteGaugePhase hQ c).meromorphicOn

theorem divisorHermiteGaugeRepresentative_order
    (g Q : ℂ → ℂ) (hQ : AnalyticOnNhd ℂ Q Set.univ) (c : ℝ) (z : ℂ) :
    meromorphicOrderAt (divisorHermiteGaugeRepresentative g Q c) z =
      meromorphicOrderAt g z := by
  have hunit := meromorphicOrderAt_mul_analyticUnit_eq
    (f := g) (u := divisorHermiteGaugePhase Q c)
    (analyticOnNhd_divisorHermiteGaugePhase hQ c z (Set.mem_univ z))
    (divisorHermiteGaugePhase_ne_zero Q c z)
  change meromorphicOrderAt (g * divisorHermiteGaugePhase Q c) z = meromorphicOrderAt g z
  rw [mul_comm]
  exact hunit

theorem realizesMero_divisorHermiteGaugeRepresentative
    {G : meroField Set.univ} {g Q : ℂ → ℂ} (hg : RealizesMero G g)
    (hQ : AnalyticOnNhd ℂ Q Set.univ) (c : ℝ) :
    RealizesMero (divisorHermiteGaugeElement G Q hQ c)
      (divisorHermiteGaugeRepresentative g Q c) := by
  obtain ⟨a, b, A, B, hb0, hA, hB, hAa, hBb, hGab, hgAB⟩ := hg
  let P : ℂ → ℂ := divisorHermiteGaugePhase Q c
  have hP : AnalyticOnNhd ℂ P Set.univ := analyticOnNhd_divisorHermiteGaugePhase hQ c
  refine ⟨a * analyticFunctionElement P hP, b, A * P, B, hb0,
    hA.mul hP, hB, ?_, hBb, ?_, fun z hBz => ?_⟩
  · rw [map_mul, hAa]
    rfl
  · rw [divisorHermiteGaugeElement, hGab]
    change (algebraMap (analyticSubring Set.univ) (meroField Set.univ) a /
        algebraMap (analyticSubring Set.univ) (meroField Set.univ) b) *
      algebraMap (analyticSubring Set.univ) (meroField Set.univ)
        (analyticFunctionElement P hP) = _
    rw [map_mul]
    ring
  · change g z * P z = (A z * P z) / B z
    rw [hgAB z hBz]
    field_simp

theorem divisorHermiteGaugeRepresentative_jet
    {S : Set ℂ} {m : S → ℕ} {g Q : ℂ → ℂ}
    (hQ : AnalyticOnNhd ℂ Q Set.univ)
    (hQorder : ∀ a : S, (m a + 1 : ℕ∞) ≤ analyticOrderAt Q a)
    (hg : ∀ a : S, AnalyticAt ℂ g a) (c : ℝ) (a : S) {j : ℕ} (hj : j ≤ m a) :
    iteratedDeriv j (divisorHermiteGaugeRepresentative g Q c) a =
      iteratedDeriv j g a := by
  by_cases hc : c = 0
  · subst c
    rw [divisorHermiteGaugeRepresentative_zero]
  have hphase : AnalyticAt ℂ (divisorHermiteGaugePhase Q c) a :=
    analyticOnNhd_divisorHermiteGaugePhase hQ c a (Set.mem_univ a)
  have hminus : AnalyticAt ℂ (fun z => divisorHermiteGaugePhase Q c z - 1) a :=
    hphase.sub analyticAt_const
  have horder : (m a + 1 : ℕ∞) ≤
      analyticOrderAt (fun z => divisorHermiteGaugePhase Q c z - 1) a := by
    exact htPassportGauge_preserves_order hQ (hQorder a) hc
  have hvanish : ∀ k < m a + 1,
      iteratedDeriv k (fun z => divisorHermiteGaugePhase Q c z - 1) a = 0 := by
    exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hminus).1 horder
  have hprod : iteratedDeriv j
      (fun z => g z * (divisorHermiteGaugePhase Q c z - 1)) a = 0 := by
    change iteratedDeriv j (g * fun z => divisorHermiteGaugePhase Q c z - 1) a = 0
    rw [iteratedDeriv_mul (hg a).contDiffAt hminus.contDiffAt]
    apply Finset.sum_eq_zero
    intro i hi
    have hij : i ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hflat : j - i < m a + 1 := by omega
    rw [hvanish (j - i) hflat]
    simp
  have hfg : AnalyticAt ℂ (divisorHermiteGaugeRepresentative g Q c) a :=
    (hg a).mul hphase
  have hsub : iteratedDeriv j
      (fun z => divisorHermiteGaugeRepresentative g Q c z - g z) a = 0 := by
    have heq : (fun z => divisorHermiteGaugeRepresentative g Q c z - g z) =
        (fun z => g z * (divisorHermiteGaugePhase Q c z - 1)) := by
      funext z
      simp only [divisorHermiteGaugeRepresentative]
      ring
    rw [heq]
    exact hprod
  have hderivSub : iteratedDeriv j
      (fun z => divisorHermiteGaugeRepresentative g Q c z - g z) a =
      iteratedDeriv j (divisorHermiteGaugeRepresentative g Q c) a -
        iteratedDeriv j g a := by
    change iteratedDeriv j
        (divisorHermiteGaugeRepresentative g Q c - g) a = _
    exact iteratedDeriv_sub hfg.contDiffAt (hg a).contDiffAt
  rw [hderivSub] at hsub
  exact sub_eq_zero.mp hsub

/-- The project-native observation fiber: a global meromorphic-field element together with an
actual meromorphic realization having the base divisor and the prescribed Hermite table. -/
def DivisorHermiteObservationFiber (g : ℂ → ℂ) (S : Set ℂ) (m : S → ℕ) :
    Set (meroField Set.univ) :=
  {X | ∃ f : ℂ → ℂ,
    RealizesMero X f ∧
    (∀ z, meromorphicOrderAt f z = meromorphicOrderAt g z) ∧
    (∀ a : S, AnalyticAt ℂ f a) ∧
    (∀ (a : S) (j : ℕ), j ≤ m a → iteratedDeriv j f a = iteratedDeriv j g a)}

theorem divisorHermiteGaugeElement_mem_observationFiber
    {S : Set ℂ} {m : S → ℕ} {G : meroField Set.univ} {g Q : ℂ → ℂ}
    (hgReal : RealizesMero G g) (hgAn : ∀ a : S, AnalyticAt ℂ g a)
    (hQ : AnalyticOnNhd ℂ Q Set.univ)
    (hQorder : ∀ a : S, (m a + 1 : ℕ∞) ≤ analyticOrderAt Q a)
    (c : ℝ) :
    divisorHermiteGaugeElement G Q hQ c ∈ DivisorHermiteObservationFiber g S m := by
  refine ⟨divisorHermiteGaugeRepresentative g Q c,
    realizesMero_divisorHermiteGaugeRepresentative hgReal hQ c,
    fun z => divisorHermiteGaugeRepresentative_order g Q hQ c z,
    fun a => (hgAn a).mul
      (analyticOnNhd_divisorHermiteGaugePhase hQ c a (Set.mem_univ a)),
    fun a j hj => divisorHermiteGaugeRepresentative_jet hQ hQorder hgAn c a hj⟩

/-- At most one exceptional parameter can be avoided by an explicit injective real curve. -/
theorem exists_injective_hypertranscendental_divisorHermiteGaugeParameters
    {G : meroField Set.univ} (hGne : G ≠ 0)
    {Q : ℂ → ℂ} (hQ : AnalyticOnNhd ℂ Q Set.univ)
    (hQHT : Hypertranscendental Q) :
    ∃ φ : ℝ → ℝ, Function.Injective φ ∧
      ∀ t, HypertranscendentalOver (RatFunc ℂ)
        (divisorHermiteGaugeElement G Q hQ (φ t)) := by
  let E : Set ℝ := {c | DifferentialAlgebraicOver (RatFunc ℂ)
    (divisorHermiteGaugeElement G Q hQ c)}
  have hEsub : E.Subsingleton :=
    divisorHermiteGaugeElement_parameterSet_subsingleton hGne hQ hQHT
  by_cases hEne : E.Nonempty
  · obtain ⟨e, he⟩ := hEne
    refine ⟨fun t => e + Real.exp t, ?_, ?_⟩
    · intro s t hst
      apply Real.exp_injective
      exact add_left_cancel hst
    · intro t hbad
      have heq : e + Real.exp t = e := hEsub hbad he
      have hexp : Real.exp t = 0 := by linarith
      exact (Real.exp_ne_zero t) hexp
  · refine ⟨fun t => t, Function.injective_id, ?_⟩
    intro t hbad
    exact hEne ⟨t, hbad⟩

/-- A nonzero global meromorphic function with any closed-discrete, sitewise-finite Hermite
passport has an injective continuum of HT representatives in the exact same observation fiber.
If the base is DA, parameter zero is the base and every nonzero parameter is HT. -/
theorem exists_divisorHermite_hypertranscendental_saturation
    {S : Set ℂ} (hSd : IsDiscrete S) (hSc : IsClosed S) (m : S → ℕ)
    {G : meroField Set.univ} (hGne : G ≠ 0) {g : ℂ → ℂ}
    (hgReal : RealizesMero G g) (hgAn : ∀ a : S, AnalyticAt ℂ g a) :
    ∃ (Q : ℂ → ℂ) (φ : ℝ → ℝ) (hQ : AnalyticOnNhd ℂ Q Set.univ),
      SchwarzRealGauge Q ∧
      Hypertranscendental Q ∧
      (∀ a : S, (m a + 1 : ℕ∞) ≤ analyticOrderAt Q a) ∧
      Function.Injective φ ∧
      Function.Injective (fun t => divisorHermiteGaugeElement G Q hQ (φ t)) ∧
      Cardinal.mk (Set.range (fun t => divisorHermiteGaugeElement G Q hQ (φ t))) =
        Cardinal.continuum ∧
      (∀ t, HypertranscendentalOver (RatFunc ℂ)
        (divisorHermiteGaugeElement G Q hQ (φ t))) ∧
      (∀ t, divisorHermiteGaugeElement G Q hQ (φ t) ∈
        DivisorHermiteObservationFiber g S m) ∧
      (∀ _hGDA : DifferentialAlgebraicOver (RatFunc ℂ) G,
        divisorHermiteGaugeElement G Q hQ 0 = G ∧
        ∀ c : ℝ, c ≠ 0 → HypertranscendentalOver (RatFunc ℂ)
          (divisorHermiteGaugeElement G Q hQ c)) := by
  obtain ⟨Q, hQ, hQreal, hQHT, hQne, hQorder⟩ :=
    exists_symmetric_hypertranscendental_passport_exponent hSd hSc m
  obtain ⟨φ, hφ, hφHT⟩ :=
    exists_injective_hypertranscendental_divisorHermiteGaugeParameters hGne hQ hQHT
  have hfamily : Function.Injective
      (fun t => divisorHermiteGaugeElement G Q hQ (φ t)) :=
    (injective_divisorHermiteGaugeElement hGne hQ hQHT).comp hφ
  have hcard : Cardinal.mk
      (Set.range (fun t => divisorHermiteGaugeElement G Q hQ (φ t))) =
      Cardinal.continuum := by
    rw [Cardinal.mk_range_eq _ hfamily, Cardinal.mk_real]
  refine ⟨Q, φ, hQ, hQreal, hQHT, hQorder, hφ, hfamily, hcard,
    hφHT, fun t => divisorHermiteGaugeElement_mem_observationFiber
      hgReal hgAn hQ hQorder (φ t), ?_⟩
  intro hGDA
  exact ⟨divisorHermiteGaugeElement_zero G Q hQ,
    fun c hc => hypertranscendentalOver_divisorHermiteGaugeElement_of_base_DA
      hGne hGDA hQ hQHT hc⟩

theorem eq_of_frequently_divisorHermite_values
    {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (hg : AnalyticOnNhd ℂ g Set.univ) {a : ℂ}
    (h : ∃ᶠ z in 𝓝[≠] a, f z = g z) : f = g := by
  funext z
  exact hf.eqOn_of_preconnected_of_frequently_eq hg isPreconnected_univ
    (Set.mem_univ a) h (Set.mem_univ z)

theorem eq_of_full_divisorHermite_germ
    {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (hg : AnalyticOnNhd ℂ g Set.univ) {a : ℂ}
    (h : ∀ k, iteratedDeriv k f a = iteratedDeriv k g a) : f = g := by
  funext z
  exact eqOn_of_iteratedDeriv_eq isPreconnected_univ hf hg (Set.mem_univ a) h
    (Set.mem_univ z)

end

end GaloisForLFunctions.RHTower
