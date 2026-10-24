import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheApertureFlowNeverStalls
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.VanishingApertureFloorAndGradedTransport
import GaloisForLFunctions.ArithmeticCompensationTheory.TheApertureFloorMustDecayDoublyExponentially
import GaloisForLFunctions.ArithmeticCriticalityTheory.ThreeTenthsSharpGaugeWeilPositivity

/-!
# The prime-shell beta function of the aperture flow

One step `a → b` of the restricted Weil ground-energy flow splits into a geometric step and an
arithmetic step. Freeze the primes at the cutoff `N = ⌊e^{2a}⌋`: the **frozen family** keeps every
prime power `n ≤ N` and drops the rest (`frozenFamily`). It is an aperture family, it agrees with
the literal flow at every aperture `c` with `⌊e^{2c}⌋ ≤ N`, and at a larger aperture it differs
from the literal form by exactly the **prime-shell correlation**

`σ_{N}(f) = Σ_{N < n ≤ e^{2c}} Λ(n) n^{-1/2} Re(⟨τ_{log n} f, f⟩ + ⟨τ_{-log n} f, f⟩)`

of the prime powers with `log n` in the shell `(2a, 2c]` (`frozenFamily_Q_eq`,
`primeShellCorrelation_eq_primeSum`).

* **Two-step renormalization law.** `μ(a) − μ(b)` is the geometric jump of the frozen flow, a
  nonnegative relaxation energy governed by the shell-flux law of `TheApertureFlowIsAShellFlux`,
  plus the arithmetic jump `μ^{[N]}(b) − μ(b)`, which lies between the shell correlations of the
  two ground states (`primeShell_sandwich`, `apertureFlow_step_eq_geometric_add_arithmetic`).
* **The shell term reads only the collars.** Each shell term pairs the restriction of `f` to the
  left collar `[−c, c − 2a]` with its restriction to the right collar `[2a − c, c]`
  (`inner_logTranslation_eq_collar`, `primeShellCorrelation_eq_collar`): the beta function is a
  signed prime-pair correlation across the shell.
* **Class III.** Under RH the literal flow obeys a relative law `μ(b) ≥ q μ(a)` with nonnegative
  factors, and conversely; but along every one-prime perturbation of ζ (any scale `x ≥ 2`, any
  weight `w ≠ 0`) no relative law with nonnegative factors holds (`relativeFluxLaw_isClassIII`).
  A flux law that does not read the exact weight of every prime is false.
* **The ceiling forces a doubly exponential rate.** No law `μ(b) ≥ e^{−C(b − a₀)} μ(a₀)` with
  `μ(a₀) > 0` holds (`not_exponential_relative_law`).
* **First rung.** A graded bound on the relaxation energy, the jump of the flow, along apertures
  with bounded gaps gives `zetaZeroWidth ≤ σ` (`zetaZeroWidth_le_of_graded_relaxation`).

The estimate itself, a bound on the arithmetic jump relative to `μ` from an input that does not
presuppose the floor, is not proved here; by `relativeFluxLaw_isClassIII` it is RH.
-/

open Complex MeasureTheory Set Filter Finset
open scoped InnerProduct

noncomputable section

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

open _root_.Zeta23 _root_.RHTower _root_.RHTower.WeilDeletion GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.SquareRootThreshold GaloisForLFunctions.ArithmeticCriticalityTheory
open GaloisForLFunctions.ArithmeticCompensationTheory

/-! ## The prime shell above a cutoff -/

/-- The visible prime blocks of the prime powers `N < n ≤ e^{2c}`. -/
def primeShellBlock (N : ℕ) (c : SuzukiPositiveAperture) :
    suzukiApertureHilbert c →L[ℂ] suzukiApertureHilbert c :=
  ∑ n ∈ Ioc N (Nat.floor (Real.exp (2 * c.1))), ccmVisiblePrimeBlock c n

theorem primeShellBlock_isSelfAdjoint (N : ℕ) (c : SuzukiPositiveAperture) :
    IsSelfAdjoint (primeShellBlock N c) := by
  classical
  unfold primeShellBlock
  generalize Finset.Ioc N (Nat.floor (Real.exp (2 * c.1))) = s
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, ContinuousLinearMap.isSelfAdjoint_iff',
      ContinuousLinearMap.adjoint.map_zero]
  | insert n s hn ih =>
    have h1 := ccmVisiblePrimeBlock_isSelfAdjoint c n
    rw [ContinuousLinearMap.isSelfAdjoint_iff'] at h1 ih ⊢
    rw [Finset.sum_insert hn, ContinuousLinearMap.adjoint.map_add, h1, ih]

/-- The **prime-shell correlation** `σ_N(f) = Re⟨S_N f, f⟩` of the prime powers above `N`. -/
def primeShellCorrelation (N : ℕ) (c : SuzukiPositiveAperture) (f : suzukiApertureHilbert c) :
    ℝ :=
  (inner ℂ (primeShellBlock N c f) f).re

theorem primeShellCorrelation_eq_sum (N : ℕ) (c : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert c) :
    primeShellCorrelation N c f =
      ∑ n ∈ Ioc N (Nat.floor (Real.exp (2 * c.1))), (inner ℂ (ccmVisiblePrimeBlock c n f) f).re := by
  rw [primeShellCorrelation, primeShellBlock, _root_.sum_apply, sum_inner, re_sum]

/-- **The shell correlation as a prime sum.** For `N ≥ 1` every index of the shell is a visible
prime power, so `σ_N` is the signed von Mangoldt correlation at the shell lags `log n`. -/
theorem primeShellCorrelation_eq_primeSum {N : ℕ} (hN : 1 ≤ N) (c : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert c) :
    primeShellCorrelation N c f =
      ∑ n ∈ Ioc N (Nat.floor (Real.exp (2 * c.1))),
        (ArithmeticFunction.vonMangoldt n : ℝ) * (1 / Real.sqrt n) *
          (inner ℂ (logTranslationCLM (Real.log n) f.1) f.1 +
            inner ℂ (logTranslationCLM (-Real.log n) f.1) f.1).re := by
  rw [primeShellCorrelation_eq_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_Ioc] at hn
  exact re_inner_visiblePrimeBlock_eq c n f (Finset.mem_Icc.mpr ⟨by omega, hn.2⟩)

/-- The shell correlation is aperture compatible: prime powers invisible at the smaller aperture
pair to zero with vectors supported there. -/
theorem primeShellCorrelation_eq_of_val_eq (N : ℕ) {a b : SuzukiPositiveAperture}
    (hab : a.1 ≤ b.1) {u : CCMArchimedeanFormDomain a} {v : CCMArchimedeanFormDomain b}
    (hvu : v.1 = u.1) :
    primeShellCorrelation N b (ccmArchimedeanFormToAperture b v) =
      primeShellCorrelation N a (ccmArchimedeanFormToAperture a u) := by
  rw [primeShellCorrelation_eq_sum, primeShellCorrelation_eq_sum,
    Finset.sum_congr rfl fun n _ => deleted_diagonal_eq_of_val_eq n hab hvu]
  have hfloor : Nat.floor (Real.exp (2 * a.1)) ≤ Nat.floor (Real.exp (2 * b.1)) :=
    Nat.floor_mono (Real.exp_le_exp.mpr (by linarith))
  symm
  refine Finset.sum_subset (Finset.Ioc_subset_Ioc_right hfloor) fun n hnb hna => ?_
  have hinv : n ∉ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))) := by
    intro hmem
    apply hna
    rw [Finset.mem_Ioc] at hnb ⊢
    exact ⟨hnb.1, (Finset.mem_Icc.mp hmem).2⟩
  rw [ccmVisiblePrimeBlock_of_invisible a hinv]
  simp

/-! ## The frozen-prime family -/

/-- The literal remainder with every prime power above `N` removed. -/
def frozenRemainder (N : ℕ) (c : SuzukiPositiveAperture) :
    suzukiApertureHilbert c →L[ℂ] suzukiApertureHilbert c :=
  ccmRestrictedWeilBoundedRemainder c + primeShellBlock N c

theorem frozenRemainder_isSelfAdjoint (N : ℕ) (c : SuzukiPositiveAperture) :
    IsSelfAdjoint (frozenRemainder N c) := by
  have h1 := ccmRestrictedWeilBoundedRemainder_isSelfAdjoint c
  have h2 := primeShellBlock_isSelfAdjoint N c
  rw [ContinuousLinearMap.isSelfAdjoint_iff'] at h1 h2 ⊢
  rw [frozenRemainder, ContinuousLinearMap.adjoint.map_add, h1, h2]

/-- The **frozen-prime family**: the restricted Weil operator that keeps only the prime powers
`n ≤ N`, at every aperture. -/
def frozenFamily (N : ℕ) : CCMRemainderFamily where
  B c := frozenRemainder N c
  selfAdjoint c := frozenRemainder_isSelfAdjoint N c
  compat := by
    intro a b hab u v hvu
    unfold frozenRemainder
    rw [add_apply, add_apply, inner_add_left,
      inner_add_left, Complex.add_re, Complex.add_re, literal_diagonal_eq_of_val_eq hab hvu]
    congr 1
    exact primeShellCorrelation_eq_of_val_eq N hab hvu

/-- The frozen form is the literal form plus the shell correlation. -/
theorem frozenFamily_B (N : ℕ) (c : SuzukiPositiveAperture) :
    (frozenFamily N).B c = frozenRemainder N c := rfl

theorem literalFamily_B (c : SuzukiPositiveAperture) :
    literalFamily.B c = ccmRestrictedWeilBoundedRemainder c := rfl

theorem frozenFamily_Q_eq (N : ℕ) (c : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain c) :
    (frozenFamily N).Q c u =
      literalFamily.Q c u + primeShellCorrelation N c (ccmArchimedeanFormToAperture c u) := by
  rw [CCMRemainderFamily.Q, CCMRemainderFamily.Q, CCMRemainderFamily.diagonal,
    CCMRemainderFamily.diagonal, frozenFamily_B, literalFamily_B, frozenRemainder, add_apply,
    inner_add_left, Complex.add_re, primeShellCorrelation]
  ring

/-- Two families with the same quadratic form at an aperture have the same ground energy there. -/
theorem energy_eq_of_Q_eq (F G : CCMRemainderFamily) (c : SuzukiPositiveAperture)
    (h : ∀ u, F.Q c u = G.Q c u) : F.energy c = G.energy c := by
  have key : ∀ F G : CCMRemainderFamily, (∀ u, F.Q c u = G.Q c u) → F.energy c ≤ G.energy c :=
    fun F G h => by
      have hf := F.energy_mul_formNorm_sq_le c (G.normalizedGround c)
      rwa [h, G.normalizedGround_Q, G.norm_normalizedGround_embedding, one_pow, mul_one] at hf
  exact le_antisymm (key F G h) (key G F fun u => (h u).symm)

/-- Below the cutoff the frozen flow is the literal flow. -/
theorem frozenFamily_energy_eq_of_floor_le {N : ℕ} {c : SuzukiPositiveAperture}
    (h : Nat.floor (Real.exp (2 * c.1)) ≤ N) :
    (frozenFamily N).energy c = ccmRestrictedWeilGroundEnergy c := by
  refine energy_eq_of_Q_eq (frozenFamily N) literalFamily c fun u => ?_
  rw [frozenFamily_Q_eq, primeShellCorrelation_eq_sum, Finset.Ioc_eq_empty_of_le h,
    Finset.sum_empty, add_zero]

/-- The cutoff that freezes the primes visible at aperture `a`. -/
abbrev primeCutoff (a : SuzukiPositiveAperture) : ℕ := Nat.floor (Real.exp (2 * a.1))

theorem one_le_primeCutoff (a : SuzukiPositiveAperture) : 1 ≤ primeCutoff a := by
  apply Nat.le_floor
  have : (1 : ℝ) ≤ Real.exp (2 * a.1) := Real.one_le_exp (by linarith [a.2])
  exact_mod_cast this

/-! ## The two-step renormalization law -/

/-- **The arithmetic jump is sandwiched by the shell correlations.** At any aperture `b`,
`σ_N(u^{[N]}_b) ≤ μ^{[N]}(b) − μ(b) ≤ σ_N(u_b)`. -/
theorem primeShell_sandwich (N : ℕ) (b : SuzukiPositiveAperture) :
    primeShellCorrelation N b
        (ccmArchimedeanFormToAperture b ((frozenFamily N).normalizedGround b)) ≤
      (frozenFamily N).energy b - ccmRestrictedWeilGroundEnergy b ∧
    (frozenFamily N).energy b - ccmRestrictedWeilGroundEnergy b ≤
      primeShellCorrelation N b
        (ccmArchimedeanFormToAperture b (literalFamily.normalizedGround b)) := by
  constructor
  · have h := literalFamily.energy_mul_formNorm_sq_le b ((frozenFamily N).normalizedGround b)
    have hQ := frozenFamily_Q_eq N b ((frozenFamily N).normalizedGround b)
    rw [(frozenFamily N).normalizedGround_Q] at hQ
    rw [(frozenFamily N).norm_normalizedGround_embedding, one_pow, mul_one] at h
    change ccmRestrictedWeilGroundEnergy b ≤ _ at h
    linarith
  · have h := (frozenFamily N).energy_mul_formNorm_sq_le b (literalFamily.normalizedGround b)
    rw [frozenFamily_Q_eq, literalFamily.normalizedGround_Q,
      literalFamily.norm_normalizedGround_embedding, one_pow, mul_one] at h
    change _ ≤ ccmRestrictedWeilGroundEnergy b + _ at h
    linarith

/-- **The two-step renormalization law.** For `a ≤ b` and the cutoff `N = ⌊e^{2a}⌋`, the jump of
the flow is the geometric jump of the frozen flow, which is the relaxation energy of the frozen
ground state, plus the arithmetic jump, which lies between the shell correlations of the frozen
and the literal ground state at `b`. -/
theorem apertureFlow_step_eq_geometric_add_arithmetic {a b : SuzukiPositiveAperture}
    (hab : a.1 ≤ b.1) :
    ccmRestrictedWeilGroundEnergy a - ccmRestrictedWeilGroundEnergy b =
        ((frozenFamily (primeCutoff a)).energy a - (frozenFamily (primeCutoff a)).energy b) +
          ((frozenFamily (primeCutoff a)).energy b - ccmRestrictedWeilGroundEnergy b) ∧
      (∀ c : ℂ,
        (frozenFamily (primeCutoff a)).energy a - (frozenFamily (primeCutoff a)).energy b =
          (shiftedForm (frozenFamily (primeCutoff a)) b ((frozenFamily (primeCutoff a)).energy b)
            (apertureExt hab ((frozenFamily (primeCutoff a)).normalizedGround a) -
              c • (frozenFamily (primeCutoff a)).normalizedGround b)
            (apertureExt hab ((frozenFamily (primeCutoff a)).normalizedGround a) -
              c • (frozenFamily (primeCutoff a)).normalizedGround b)).re) ∧
      0 ≤ (frozenFamily (primeCutoff a)).energy a - (frozenFamily (primeCutoff a)).energy b ∧
      primeShellCorrelation (primeCutoff a) b (ccmArchimedeanFormToAperture b
          ((frozenFamily (primeCutoff a)).normalizedGround b)) ≤
        (frozenFamily (primeCutoff a)).energy b - ccmRestrictedWeilGroundEnergy b ∧
      (frozenFamily (primeCutoff a)).energy b - ccmRestrictedWeilGroundEnergy b ≤
        primeShellCorrelation (primeCutoff a) b
          (ccmArchimedeanFormToAperture b (literalFamily.normalizedGround b)) := by
  have ha : (frozenFamily (primeCutoff a)).energy a = ccmRestrictedWeilGroundEnergy a :=
    frozenFamily_energy_eq_of_floor_le le_rfl
  obtain ⟨h1, h2⟩ := primeShell_sandwich (primeCutoff a) b
  refine ⟨by rw [ha]; ring, energy_sub_energy_eq_shiftedForm _ hab,
    sub_nonneg.mpr ((frozenFamily (primeCutoff a)).energy_antitone hab), h1, h2⟩

/-! ## The shell term reads only the collars -/

/-- **Collar localization of a translation pairing.** For `f` supported in `[−c, c]` and a lag
`t ≥ 0`, `⟨τ_t f, f⟩` only sees `f` on `[t − c, c]` (shifted) and on `[−c, c − t]`; any larger
collars `R ⊇ [t − c, c]`, `L ⊇ [−c, c − t]` may be cut out. -/
theorem inner_logTranslation_eq_collar (c : SuzukiPositiveAperture) (f : suzukiApertureHilbert c)
    {t : ℝ} {L R : Set ℝ} (hL : MeasurableSet L) (hR : MeasurableSet R)
    (hLsub : Icc (-c.1) (c.1 - t) ⊆ L) (hRsub : Icc (t - c.1) c.1 ⊆ R) :
    inner ℂ (logTranslationCLM t f.1) f.1 =
      inner ℂ (logTranslationCLM t (indicatorCutoff R hR f.1)) (indicatorCutoff L hL f.1) := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  have hfix : indicatorCutoff (centralInterval c.1) (measurableSet_centralInterval c.1) f.1 = f.1 :=
    indicatorCutoff_suzukiApertureHilbert c f
  have hfixAE : (f.1 : ℝ → ℂ) =ᵐ[volume] (centralInterval c.1).indicator (fun y => f.1 y) := by
    have h := indicatorCutoff_ae (centralInterval c.1) (measurableSet_centralInterval c.1) f.1
    rw [hfix] at h
    exact h
  have hqmp := (MellinL2.realTranslation_measurePreserving t).quasiMeasurePreserving.tendsto_ae
  have hfixShift := hfixAE.comp_tendsto hqmp
  have hRShift := (indicatorCutoff_ae R hR f.1).comp_tendsto hqmp
  have hLAE := indicatorCutoff_ae L hL f.1
  have htransf := Lp.coeFn_compMeasurePreserving f.1 (MellinL2.realTranslation_measurePreserving t)
  have htransR := Lp.coeFn_compMeasurePreserving (indicatorCutoff R hR f.1)
    (MellinL2.realTranslation_measurePreserving t)
  apply integral_congr_ae
  filter_upwards [hfixAE, hfixShift, hRShift, hLAE, htransf, htransR] with
      x hx0 hxt hRx hLx htf htR
  have htf' : logTranslationCLM t f.1 x = f.1 (x + t) := by
    simpa [logTranslationCLM, MellinL2.additiveTranslationUnitary,
      MellinL2.realTranslationEquiv, Function.comp_apply] using! htf
  have htR' : logTranslationCLM t (indicatorCutoff R hR f.1) x =
      indicatorCutoff R hR f.1 (x + t) := by
    simpa [logTranslationCLM, MellinL2.additiveTranslationUnitary,
      MellinL2.realTranslationEquiv, Function.comp_apply] using! htR
  have hxt' : f.1 (x + t) = (centralInterval c.1).indicator (fun y => f.1 y) (x + t) := by
    simpa [MellinL2.realTranslationEquiv, Function.comp_apply] using hxt
  have hRx' : indicatorCutoff R hR f.1 (x + t) = R.indicator (fun y => f.1 y) (x + t) := by
    simpa [MellinL2.realTranslationEquiv, Function.comp_apply] using hRx
  rw [htf', htR', hRx', hLx]
  by_cases hx : x ∈ centralInterval c.1
  · by_cases hxt2 : x + t ∈ centralInterval c.1
    · rw [centralInterval, Set.mem_Icc] at hx hxt2
      have hxL : x ∈ L := hLsub ⟨hx.1, by linarith [hxt2.2]⟩
      have hxR : x + t ∈ R := hRsub ⟨by linarith [hx.1], hxt2.2⟩
      rw [Set.indicator_of_mem hxL, Set.indicator_of_mem hxR]
    · have hz : f.1 (x + t) = 0 := by rw [hxt', Set.indicator_of_notMem hxt2]
      have hzR : R.indicator (fun y => f.1 y) (x + t) = 0 := by
        by_cases hm : x + t ∈ R
        · rw [Set.indicator_of_mem hm, hz]
        · rw [Set.indicator_of_notMem hm]
      rw [hz, hzR, inner_zero_left, inner_zero_left]
  · have hz : f.1 x = 0 := by rw [hx0, Set.indicator_of_notMem hx]
    have hzL : L.indicator (fun y => f.1 y) x = 0 := by
      by_cases hm : x ∈ L
      · rw [Set.indicator_of_mem hm, hz]
      · rw [Set.indicator_of_notMem hm]
    rw [hz, hzL, inner_zero_right, inner_zero_right]

/-- The symmetric translation pairing reads twice the real collar pairing. -/
theorem re_symmetric_logTranslation_eq_collar (c : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert c) {t : ℝ} {L R : Set ℝ} (hL : MeasurableSet L)
    (hR : MeasurableSet R) (hLsub : Icc (-c.1) (c.1 - t) ⊆ L) (hRsub : Icc (t - c.1) c.1 ⊆ R) :
    (inner ℂ (logTranslationCLM t f.1) f.1 + inner ℂ (logTranslationCLM (-t) f.1) f.1).re =
      2 * (inner ℂ (logTranslationCLM t (indicatorCutoff R hR f.1))
        (indicatorCutoff L hL f.1)).re := by
  have hneg : inner ℂ (logTranslationCLM (-t) f.1) f.1 =
      (starRingEnd ℂ) (inner ℂ (logTranslationCLM t f.1) f.1) := by
    rw [inner_logTranslationCLM (-t), neg_neg, inner_conj_symm f.1 (logTranslationCLM t f.1)]
  rw [hneg, Complex.add_re, Complex.conj_re, ← inner_logTranslation_eq_collar c f hL hR hLsub hRsub]
  ring

/-- **The shell correlation is a cross-collar prime-pair correlation.** With the cutoff
`N = ⌊e^{2a}⌋` every shell lag exceeds `2a`, so each term pairs `f` on the left collar
`[−c, c − 2a]` with `f` on the right collar `[2a − c, c]`. -/
theorem primeShellCorrelation_eq_collar (a c : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert c) :
    primeShellCorrelation (primeCutoff a) c f =
      ∑ n ∈ Ioc (primeCutoff a) (Nat.floor (Real.exp (2 * c.1))),
        (ArithmeticFunction.vonMangoldt n : ℝ) * (1 / Real.sqrt n) *
          (2 * (inner ℂ (logTranslationCLM (Real.log n)
            (indicatorCutoff (Icc (2 * a.1 - c.1) c.1) measurableSet_Icc f.1))
            (indicatorCutoff (Icc (-c.1) (c.1 - 2 * a.1)) measurableSet_Icc f.1)).re) := by
  rw [primeShellCorrelation_eq_primeSum (one_le_primeCutoff a)]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_Ioc] at hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlog : 2 * a.1 < Real.log n := by
    rw [Real.lt_log_iff_exp_lt hnpos]
    exact (Nat.lt_floor_add_one _).trans_le (by exact_mod_cast Nat.succ_le_of_lt hn.1)
  rw [re_symmetric_logTranslation_eq_collar c f (t := Real.log n)
    (L := Icc (-c.1) (c.1 - 2 * a.1)) (R := Icc (2 * a.1 - c.1) c.1) measurableSet_Icc
    measurableSet_Icc (Icc_subset_Icc le_rfl (by linarith)) (Icc_subset_Icc (by linarith) le_rfl)]

/-- **Only the collars are read.** Two vectors that agree on both collars have the same shell
correlation. -/
theorem primeShellCorrelation_eq_of_collars_eq (a c : SuzukiPositiveAperture)
    {f g : suzukiApertureHilbert c}
    (hL : indicatorCutoff (Icc (-c.1) (c.1 - 2 * a.1)) measurableSet_Icc f.1 =
      indicatorCutoff (Icc (-c.1) (c.1 - 2 * a.1)) measurableSet_Icc g.1)
    (hR : indicatorCutoff (Icc (2 * a.1 - c.1) c.1) measurableSet_Icc f.1 =
      indicatorCutoff (Icc (2 * a.1 - c.1) c.1) measurableSet_Icc g.1) :
    primeShellCorrelation (primeCutoff a) c f = primeShellCorrelation (primeCutoff a) c g := by
  rw [primeShellCorrelation_eq_collar, primeShellCorrelation_eq_collar, hL, hR]

/-! ## Class III: the relative law reads every prime weight -/

/-- **The relative flux law is RH, and it fails along every one-prime perturbation.** A relative
law `q(a,b) μ(a) ≤ μ(b)` with nonnegative factors holds along the literal flow iff RH; along the
flow of ζ with any nonzero weight `w` added at any scale `x ≥ 2`, no such law holds. -/
theorem relativeFluxLaw_isClassIII :
    (RiemannHypothesis ↔ ∃ q : SuzukiPositiveAperture → SuzukiPositiveAperture → ℝ,
      (∀ a b, 0 ≤ q a b) ∧ ∀ a b : SuzukiPositiveAperture, a.1 ≤ b.1 →
        q a b * ccmRestrictedWeilGroundEnergy a ≤ ccmRestrictedWeilGroundEnergy b) ∧
    ∀ {x w : ℝ}, 2 ≤ x → w ≠ 0 → ∀ q : SuzukiPositiveAperture → SuzukiPositiveAperture → ℝ,
      (∀ a b, 0 ≤ q a b) → ¬ ∀ a b : SuzukiPositiveAperture, a.1 ≤ b.1 →
        q a b * ccmInsertedGroundEnergy a x w ≤ ccmInsertedGroundEnergy b x w := by
  refine ⟨⟨fun hRH => ?_, fun ⟨q, hq, hlaw⟩ => ?_⟩, fun {x w} hx hw q hq hlaw => ?_⟩
  · have hpos := riemannHypothesis_iff_ccmRestrictedWeilGroundEnergy_pos.mp hRH
    refine ⟨fun a b => ccmRestrictedWeilGroundEnergy b / ccmRestrictedWeilGroundEnergy a,
      fun a b => (div_pos (hpos b) (hpos a)).le, fun a b _ => ?_⟩
    exact (div_mul_cancel₀ _ (hpos a).ne').le
  · let a₀ : SuzukiPositiveAperture := ⟨3 / 10, by norm_num⟩
    have h0 : 0 < ccmRestrictedWeilGroundEnergy a₀ :=
      lt_of_lt_of_le (by norm_num) (one_div_5000_le_ccmRestrictedWeilGroundEnergy_threeTenths
        (A := a₀) le_rfl)
    refine riemannHypothesis_iff_forall_ccmRestrictedWeilGroundEnergy_nonneg.mpr fun b => ?_
    rcases le_total a₀.1 b.1 with hb | hb
    · exact (mul_nonneg (hq a₀ b) h0.le).trans (hlaw a₀ b hb)
    · exact h0.le.trans (ccmRestrictedWeilGroundEnergy_antitone hb)
  · obtain ⟨δ, hδ, hpos⟩ := exists_small_aperture_ccmInsertedGroundEnergy_pos (by linarith) w
    obtain ⟨a₁, hneg⟩ : ∃ a : SuzukiPositiveAperture, ccmInsertedGroundEnergy a x w < 0 := by
      rcases lt_or_gt_of_ne hw with hn | hp
      · exact exists_ccmInsertedGroundEnergy_neg_of_neg hx hn
      · exact exists_ccmInsertedGroundEnergy_neg_of_pos (by linarith) hp
    let a₀ : SuzukiPositiveAperture := ⟨min (δ / 2) a₁.1, lt_min (by linarith) a₁.2⟩
    have h0 : 0 < ccmInsertedGroundEnergy a₀ x w :=
      hpos a₀ (lt_of_le_of_lt (min_le_left _ _) (by linarith))
    have := hlaw a₀ a₁ (min_le_right _ _)
    nlinarith [mul_nonneg (hq a₀ a₁) h0.le]

/-! ## The ceiling forces a doubly exponential rate -/

/-- **No exponential relative law.** A bound `μ(b) ≥ e^{−C(b − a₀)} μ(a₀)` with `μ(a₀) > 0` at all
larger apertures contradicts the doubly exponential ceiling. -/
theorem not_exponential_relative_law (C : ℝ) {a₀ : SuzukiPositiveAperture}
    (h0 : 0 < ccmRestrictedWeilGroundEnergy a₀) :
    ¬ ∀ b : SuzukiPositiveAperture, a₀.1 ≤ b.1 →
      Real.exp (-C * (b.1 - a₀.1)) * ccmRestrictedWeilGroundEnergy a₀ ≤
        ccmRestrictedWeilGroundEnergy b := by
  intro hlaw
  obtain ⟨K, hK, hfloor⟩ := exists_le_floorLoss_of_floor
  have hM0 : 0 ≤ |Real.log (ccmRestrictedWeilGroundEnergy a₀ / K)| + |C| * |a₀.1| + 2 * |C| :=
    by positivity
  have hm3 := le_max_right a₀.1 3
  have hma := le_max_left a₀.1 3
  let b : SuzukiPositiveAperture := ⟨max a₀.1 3 +
    (|Real.log (ccmRestrictedWeilGroundEnergy a₀ / K)| + |C| * |a₀.1| + 2 * |C| + 7),
    by linarith⟩
  have hb : b.1 = max a₀.1 3 +
      (|Real.log (ccmRestrictedWeilGroundEnergy a₀ / K)| + |C| * |a₀.1| + 2 * |C| + 7) := rfl
  have hab : a₀.1 ≤ b.1 := by rw [hb]; linarith
  have hb3 : 3 ≤ b.1 := by rw [hb]; linarith
  have hfl := hfloor b hb3 (ccmRestrictedWeilGroundEnergy a₀) (C * (b.1 - a₀.1)) h0
    (by rw [mul_comm (ccmRestrictedWeilGroundEnergy a₀)]; simpa only [neg_mul] using hlaw b hab)
  set D := Real.log (ccmRestrictedWeilGroundEnergy a₀ / K)
  have hy1 : |D| + |C| * |a₀.1| + 2 * |C| + 8 ≤ b.1 - 2 := by rw [hb]; linarith
  have hy0 : 0 ≤ 2 * (b.1 - 2) := by linarith
  have hexp := Real.quadratic_le_exp_of_nonneg hy0
  have hpi := Real.pi_gt_three
  have hsq : 6 * (b.1 - 2) ^ 2 ≤ Real.pi * Real.exp (2 * (b.1 - 2)) := by
    have h3 := mul_le_mul_of_nonneg_right hpi.le (Real.exp_pos (2 * (b.1 - 2))).le
    nlinarith
  have hCa : C * (b.1 - a₀.1) ≤ |C| * b.1 + |C| * |a₀.1| := by
    have h1 : C * (b.1 - a₀.1) ≤ |C| * |b.1 - a₀.1| := by
      rw [← abs_mul]
      exact le_abs_self _
    have h2 : |b.1 - a₀.1| ≤ b.1 + |a₀.1| := by
      rw [abs_le]
      constructor <;> linarith [abs_nonneg a₀.1, le_abs_self a₀.1, neg_abs_le a₀.1]
    nlinarith [abs_nonneg C]
  have hD := neg_abs_le D
  have hyy := mul_le_mul_of_nonneg_left hy1 (by linarith : (0 : ℝ) ≤ b.1 - 2)
  have hyD := mul_le_mul_of_nonneg_right (by linarith : (1 : ℝ) ≤ b.1 - 2) (abs_nonneg D)
  have hyC := mul_le_mul_of_nonneg_right (by linarith : (1 : ℝ) ≤ b.1 - 2) (abs_nonneg C)
  have hyCa := mul_le_mul_of_nonneg_right (by linarith : (1 : ℝ) ≤ b.1 - 2)
    (mul_nonneg (abs_nonneg C) (abs_nonneg a₀.1))
  nlinarith

/-! ## The first rung: a graded relaxation bound is a zero-free strip -/

/-- **First rung.** If along apertures `A_j → ∞` with bounded gaps the relaxation energy of each
step, `μ(A_j) − μ(A_{j+1})`, is at most the graded share `(1 − e^{2σ(A_{j+1} − A_j)}) μ(A_j)` plus a
leakage whose graded sum stays below `e^{−2σA_0} μ(A_0) + C`, then `zetaZeroWidth ≤ σ`. -/
theorem zetaZeroWidth_le_of_graded_relaxation {A : ℕ → SuzukiPositiveAperture} {δ : ℕ → ℝ}
    {σ C Δ : ℝ} (hσ : 0 ≤ σ) (hC : 0 ≤ C) (hΔ : 0 ≤ Δ)
    (hAtop : Tendsto (fun j => (A j).1) atTop atTop)
    (hgap : ∀ j, (A (j + 1)).1 ≤ (A j).1 + Δ) (hmono : ∀ j, (A j).1 ≤ (A (j + 1)).1)
    (hrelax : ∀ j,
      (shiftedForm literalFamily (A (j + 1)) (ccmRestrictedWeilGroundEnergy (A (j + 1)))
        (apertureExt (hmono j) (literalFamily.normalizedGround (A j)))
        (apertureExt (hmono j) (literalFamily.normalizedGround (A j)))).re ≤
      (1 - Real.exp (2 * σ * ((A (j + 1)).1 - (A j).1))) * ccmRestrictedWeilGroundEnergy (A j) +
        δ j)
    (hsum : ∀ J : ℕ, ∑ j ∈ range J, Real.exp (-2 * σ * (A (j + 1)).1) * δ j ≤
      Real.exp (-2 * σ * (A 0).1) * ccmRestrictedWeilGroundEnergy (A 0) + C) :
    zetaZeroWidth ≤ σ := by
  refine (zetaZeroWidth_le_of_graded_aperture_step hσ hC hΔ hAtop hgap (fun j => ?_) hsum).2.1
  have hjump : ccmRestrictedWeilGroundEnergy (A j) - ccmRestrictedWeilGroundEnergy (A (j + 1)) =
      (shiftedForm literalFamily (A (j + 1)) (ccmRestrictedWeilGroundEnergy (A (j + 1)))
        (apertureExt (hmono j) (literalFamily.normalizedGround (A j)))
        (apertureExt (hmono j) (literalFamily.normalizedGround (A j)))).re := by
    have h := energy_sub_energy_eq_shiftedForm literalFamily (hmono j) 0
    rw [zero_smul, sub_zero] at h
    exact h
  have hstep := hrelax j
  rw [← hjump] at hstep
  have hE : Real.exp (-2 * σ * (A (j + 1)).1) * Real.exp (2 * σ * ((A (j + 1)).1 - (A j).1)) =
      Real.exp (-2 * σ * (A j).1) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hEpos := Real.exp_pos (-2 * σ * (A (j + 1)).1)
  have hmul := mul_le_mul_of_nonneg_left
    (show Real.exp (2 * σ * ((A (j + 1)).1 - (A j).1)) * ccmRestrictedWeilGroundEnergy (A j) -
        δ j ≤ ccmRestrictedWeilGroundEnergy (A (j + 1)) by linarith) hEpos.le
  rw [mul_sub, ← mul_assoc, hE] at hmul
  linarith

/-! ## The crossing sits before the visibility aperture of a near-top zero -/

/-- **An off-line zero makes the flow cross zero exactly once, before it is visible.** For a
near-top zero `½ + z₀` read by the lag family at lag `V` with readout `η`, the flow has a unique
zero `a*`, positive before it and negative after it, and `a* ≤ V/2 + w`. -/
theorem groundEnergyCrossing_le_visibility {w : ℝ} (hw : 0 < w)
    {z₀ : ℂ} (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hre₀ : 0 < z₀.re)
    {η : ℝ} (hη : 0 < η) (hηle : η ≤ ‖paperFT (scaledBump w) (-(I * z₀))‖)
    {V : ℝ} (hV : oneParamLag w η z₀.re ≤ V)
    (htop : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re - 1 / 2 ≤ z₀.re + 1 / V) :
    ∃ astar : SuzukiPositiveAperture, ccmRestrictedWeilGroundEnergy astar = 0 ∧
      (∀ a : SuzukiPositiveAperture, a < astar → 0 < ccmRestrictedWeilGroundEnergy a) ∧
      (∀ a : SuzukiPositiveAperture, astar < a → ccmRestrictedWeilGroundEnergy a < 0) ∧
      (∀ a : SuzukiPositiveAperture, ccmRestrictedWeilGroundEnergy a = 0 → a = astar) ∧
      astar.1 ≤ V / 2 + w := by
  have hRH : ¬ RiemannHypothesis := fun hRH => by
    let A : SuzukiPositiveAperture := ⟨max (V / 2 + w) 0 + 1, by positivity⟩
    have hlt := lt_of_ccmRestrictedWeilGroundEnergy_nonneg_of_near_top_zero hw hz₀ hre₀ hη hηle hV
      htop (ccmRestrictedWeilGroundEnergy_nonneg_of_riemannHypothesis' hRH A)
    change max (V / 2 + w) 0 + 1 < V / 2 + w at hlt
    linarith [le_max_left (V / 2 + w) 0]
  rcases riemannHypothesis_or_unique_groundEnergyCrossing with h | ⟨astar, h0, hpos, hneg, huniq⟩
  · exact absurd h hRH
  · refine ⟨astar, h0, hpos, hneg, huniq, ?_⟩
    have hc : astar = ⟨zetaContactAperture, zetaContactAperture_pos hRH⟩ :=
      (huniq _ (ccmRestrictedWeilGroundEnergy_contact_eq_zero hRH)).symm
    rw [hc]
    exact zetaContactAperture_le_of_near_top_zero hw hz₀ hre₀ hη hηle hV htop

/-! ## Synthesis -/

/-- **Transport in aperture as a renormalization flow.** For the restricted Weil ground energy:
1. every step is a shell flux, `Φ_{a,b}(u_b) = (μ(b) − μ(a)) ⟨J ext u_a, J u_b⟩`, and the flux
   vanishes on the smaller form domain;
2. the flux of a ground state into a strictly larger aperture is never identically zero, and the
   flow is strictly decreasing;
3. one step is a geometric step of the frozen-prime flow plus an arithmetic step bracketed by the
   shell correlations of the primes with `log n ∈ (2a, 2b]`;
4. a relative flux law with nonnegative factors holds iff RH, and fails along every one-prime
   perturbation of ζ (Class III);
5. no exponential relative law is compatible with the ceiling. -/
theorem apertureRenormalizationFlow :
    (∀ {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1),
      (∀ w : CCMArchimedeanFormDomain a, shellFlux literalFamily hab (apertureExt hab w) = 0) ∧
      shellFlux literalFamily hab (literalFamily.normalizedGround b) =
        ((ccmRestrictedWeilGroundEnergy b - ccmRestrictedWeilGroundEnergy a : ℝ) : ℂ) *
          inner ℂ (ccmArchimedeanFormToAperture b
              (apertureExt hab (literalFamily.normalizedGround a)))
            (ccmArchimedeanFormToAperture b (literalFamily.normalizedGround b))) ∧
    (∀ {a b : SuzukiPositiveAperture} (hab : a.1 < b.1),
      ∃ v : CCMArchimedeanFormDomain b, shellFlux literalFamily hab.le v ≠ 0) ∧
    StrictAnti ccmRestrictedWeilGroundEnergy ∧
    (∀ {a b : SuzukiPositiveAperture}, a.1 ≤ b.1 →
      primeShellCorrelation (primeCutoff a) b (ccmArchimedeanFormToAperture b
          ((frozenFamily (primeCutoff a)).normalizedGround b)) ≤
        (frozenFamily (primeCutoff a)).energy b - ccmRestrictedWeilGroundEnergy b ∧
      (frozenFamily (primeCutoff a)).energy b - ccmRestrictedWeilGroundEnergy b ≤
        primeShellCorrelation (primeCutoff a) b
          (ccmArchimedeanFormToAperture b (literalFamily.normalizedGround b)) ∧
      (frozenFamily (primeCutoff a)).energy a = ccmRestrictedWeilGroundEnergy a) ∧
    (RiemannHypothesis ↔ ∃ q : SuzukiPositiveAperture → SuzukiPositiveAperture → ℝ,
      (∀ a b, 0 ≤ q a b) ∧ ∀ a b : SuzukiPositiveAperture, a.1 ≤ b.1 →
        q a b * ccmRestrictedWeilGroundEnergy a ≤ ccmRestrictedWeilGroundEnergy b) ∧
    (∀ {x w : ℝ}, 2 ≤ x → w ≠ 0 → ∀ q : SuzukiPositiveAperture → SuzukiPositiveAperture → ℝ,
      (∀ a b, 0 ≤ q a b) → ¬ ∀ a b : SuzukiPositiveAperture, a.1 ≤ b.1 →
        q a b * ccmInsertedGroundEnergy a x w ≤ ccmInsertedGroundEnergy b x w) ∧
    (∀ (C : ℝ) {a₀ : SuzukiPositiveAperture}, 0 < ccmRestrictedWeilGroundEnergy a₀ →
      ¬ ∀ b : SuzukiPositiveAperture, a₀.1 ≤ b.1 →
        Real.exp (-C * (b.1 - a₀.1)) * ccmRestrictedWeilGroundEnergy a₀ ≤
          ccmRestrictedWeilGroundEnergy b) :=
  ⟨fun hab => ⟨shellFlux_ext_eq_zero literalFamily hab, shellFlux_ground_eq literalFamily hab⟩,
    fun hab => exists_shellFlux_ne_zero hab, strictAnti_ccmRestrictedWeilGroundEnergy,
    fun {a b} _ => ⟨(primeShell_sandwich (primeCutoff a) b).1,
      (primeShell_sandwich (primeCutoff a) b).2, frozenFamily_energy_eq_of_floor_le le_rfl⟩,
    relativeFluxLaw_isClassIII.1, relativeFluxLaw_isClassIII.2,
    fun C _ h0 => not_exponential_relative_law C h0⟩

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
