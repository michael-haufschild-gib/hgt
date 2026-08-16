import GaloisForLFunctions.RHTower.XiMassThetaLogDiscrepancy
import GaloisForLFunctions.RHTower.XiMassShellPrimeMass
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Abel summation on a logarithmic prime window

For a continuously differentiable test `G` on `[H,T]` the Stieltjes pairing against the prime
counting step `Θ(h) = θ(e^h)` obeys the finite-atom integration-by-parts identity

`∑_{H < log p ≤ T} (log p) G(log p)
   = (Θ(T) − Θ(H)) G(T) − ∫_H^T (Θ(h) − Θ(H)) G'(h) dh`.

Subtracting the ordinary integration by parts of the continuum pairing `∫_H^T G(h) e^h dh` turns
this into the discrepancy form

`∫_{(H,T]} G dE = E(T) G(T) − E(H) G(H) − ∫_H^T E(h) G'(h) dh`,  `E = Θ − exp`,

which converts a prime-number-theorem remainder bound directly into a bound for the moving
quadrature defect on a window.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-! ## The window index set -/

/-- The window prime index set. -/
def primeLogWindow (H T : ℝ) : Finset ℕ :=
  (Finset.Ioc ⌊Real.exp H⌋₊ ⌊Real.exp T⌋₊).filter (fun p => Nat.Prime p)

theorem mem_primeLogWindow {H T : ℝ} {p : ℕ} :
    p ∈ primeLogWindow H T ↔
      (⌊Real.exp H⌋₊ < p ∧ p ≤ ⌊Real.exp T⌋₊) ∧ Nat.Prime p := by
  classical
  rw [primeLogWindow, Finset.mem_filter, Finset.mem_Ioc]

theorem primeLogWindow_log_lt {H T : ℝ} {p : ℕ} (hp : p ∈ primeLogWindow H T) :
    H < Real.log p := by
  rw [mem_primeLogWindow] at hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.2.pos
  have h1 := Nat.lt_floor_add_one (Real.exp H)
  have h2 : ((⌊Real.exp H⌋₊ : ℕ) : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast hp.1.1
  exact (Real.lt_log_iff_exp_lt hp0).2 (by linarith)

theorem primeLogWindow_log_le {H T : ℝ} {p : ℕ} (hp : p ∈ primeLogWindow H T) :
    Real.log p ≤ T := by
  rw [mem_primeLogWindow] at hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.2.pos
  have h1 : ((p : ℕ) : ℝ) ≤ ((⌊Real.exp T⌋₊ : ℕ) : ℝ) := by exact_mod_cast hp.1.2
  have h2 : ((⌊Real.exp T⌋₊ : ℕ) : ℝ) ≤ Real.exp T := Nat.floor_le (Real.exp_pos _).le
  exact (Real.log_le_iff_le_exp hp0).2 (le_trans h1 h2)

/-- The cumulative window mass is the increment of the Chebyshev step. -/
theorem sum_primeLogWindow_indicator {H T h : ℝ} (hHh : H ≤ h) (hhT : h ≤ T) :
    ∑ p ∈ primeLogWindow H T, (if Real.log p ≤ h then (Real.log p : ℝ) else 0)
      = Chebyshev.theta (Real.exp h) - Chebyshev.theta (Real.exp H) := by
  classical
  have hfl : ⌊Real.exp H⌋₊ ≤ ⌊Real.exp h⌋₊ :=
    Nat.floor_mono (Real.exp_le_exp.2 hHh)
  have hfl' : ⌊Real.exp h⌋₊ ≤ ⌊Real.exp T⌋₊ :=
    Nat.floor_mono (Real.exp_le_exp.2 hhT)
  have hfilter : (primeLogWindow H T).filter (fun p : ℕ => Real.log (p : ℝ) ≤ h)
      = (Finset.Ioc ⌊Real.exp H⌋₊ ⌊Real.exp h⌋₊).filter (fun p : ℕ => Nat.Prime p) := by
    ext p
    simp only [Finset.mem_filter, mem_primeLogWindow, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨⟨h1, _⟩, hprime⟩, hlog⟩
      refine ⟨⟨h1, ?_⟩, hprime⟩
      have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
      have hple : (p : ℝ) ≤ Real.exp h := (Real.log_le_iff_le_exp hp0).1 hlog
      exact Nat.le_floor hple
    · rintro ⟨⟨h1, h2⟩, hprime⟩
      have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
      have hple : (p : ℝ) ≤ Real.exp h :=
        le_trans (by exact_mod_cast h2) (Nat.floor_le (Real.exp_pos _).le)
      exact ⟨⟨⟨h1, le_trans h2 hfl'⟩, hprime⟩, (Real.log_le_iff_le_exp hp0).2 hple⟩
  rw [← Finset.sum_filter, hfilter, ← chebyshevTheta_sub_eq_shellSum hfl]

/-! ## Integrability of the step against a derivative -/

/-- The window step, as a complex-valued atom sum, agrees with the Chebyshev increment. -/
theorem sum_primeLogWindow_indicatorC {H T h : ℝ} (hHh : H ≤ h) (hhT : h ≤ T) :
    ∑ p ∈ primeLogWindow H T, (if Real.log p ≤ h then ((Real.log p : ℝ) : ℂ) else 0)
      = ((Chebyshev.theta (Real.exp h) - Chebyshev.theta (Real.exp H) : ℝ) : ℂ) := by
  classical
  rw [← sum_primeLogWindow_indicator hHh hhT]
  push_cast
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hph : Real.log p ≤ h <;> simp [hph]

theorem intervalIntegrable_thetaWindowStep_mul {G' : ℝ → ℂ} {H T : ℝ} (hHT : H ≤ T)
    (hG' : IntervalIntegrable G' volume H T) :
    IntervalIntegrable
      (fun h : ℝ =>
        ((Chebyshev.theta (Real.exp h) - Chebyshev.theta (Real.exp H) : ℝ) : ℂ) * G' h)
      volume H T := by
  classical
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hHT]
  have hbase : Integrable G' (volume.restrict (Ioc H T)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hHT).mp hG'
  have hstep : ∀ p ∈ primeLogWindow H T, Integrable
      (fun h : ℝ => (if Real.log p ≤ h then ((Real.log p : ℝ) : ℂ) else 0) * G' h)
      (volume.restrict (Ioc H T)) := by
    intro p _
    have hi := (hbase.const_mul ((Real.log p : ℝ) : ℂ)).indicator
      (measurableSet_Ici : MeasurableSet (Ici (Real.log p)))
    apply hi.congr
    filter_upwards with h
    by_cases hph : Real.log p ≤ h <;> simp [Set.indicator, hph]
  have hsum := MeasureTheory.integrable_finsetSum _ hstep
  apply hsum.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with h hh
  rw [← Finset.sum_mul, sum_primeLogWindow_indicatorC hh.1.le hh.2]

/-! ## Abel summation -/

/-- Integral of one logarithmic atom of the window against a derivative test. -/
private theorem integral_windowAtom_mul_deriv
    {F F' : ℝ → ℂ} {H T y : ℝ} (hHy : H < y) (hyT : y ≤ T)
    (hF : ∀ x ∈ Set.uIcc y T, HasDerivAt F (F' x) x)
    (hF' : IntervalIntegrable F' volume y T) (c : ℂ) :
    (∫ h in Ioc H T, (if y ≤ h then c else 0) * F' h) = c * (F T - F y) := by
  have hfun : (fun h : ℝ => (if y ≤ h then c else 0) * F' h)
      = (Ici y).indicator (fun h => c * F' h) := by
    funext h
    by_cases hyh : y ≤ h <;> simp [Set.indicator, hyh]
  rw [hfun, ← MeasureTheory.integral_indicator measurableSet_Ioc, Set.indicator_indicator]
  have hset : Ioc H T ∩ Ici y = Icc y T := by
    ext h
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici, Set.mem_Icc]
    constructor
    · intro hh
      exact ⟨hh.2, hh.1.2⟩
    · intro hh
      exact ⟨⟨lt_of_lt_of_le hHy hh.1, hh.2⟩, hh.1⟩
  rw [hset, MeasureTheory.integral_indicator measurableSet_Icc,
    MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hyT,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_eq_sub_of_hasDerivAt hF hF']

/-- **Abel summation on a logarithmic prime window.** -/
theorem sum_primeLogWindow_mul_eq {G G' : ℝ → ℂ} {H T : ℝ} (hHT : H ≤ T)
    (hG : ∀ x ∈ Set.Icc H T, HasDerivAt G (G' x) x)
    (hG' : IntervalIntegrable G' volume H T) :
    ∑ p ∈ primeLogWindow H T, ((Real.log p : ℝ) : ℂ) * G (Real.log p)
      = ((Chebyshev.theta (Real.exp T) - Chebyshev.theta (Real.exp H) : ℝ) : ℂ) * G T
        - ∫ h in H..T,
            ((Chebyshev.theta (Real.exp h) - Chebyshev.theta (Real.exp H) : ℝ) : ℂ) * G' h := by
  classical
  have hbase : Integrable G' (volume.restrict (Ioc H T)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hHT).mp hG'
  have hstep : ∀ p ∈ primeLogWindow H T, Integrable
      (fun h : ℝ => (if Real.log p ≤ h then ((Real.log p : ℝ) : ℂ) else 0) * G' h)
      (volume.restrict (Ioc H T)) := by
    intro p _
    have hi := (hbase.const_mul ((Real.log p : ℝ) : ℂ)).indicator
      (measurableSet_Ici : MeasurableSet (Ici (Real.log p)))
    apply hi.congr
    filter_upwards with h
    by_cases hph : Real.log p ≤ h <;> simp [Set.indicator, hph]
  have hpiece : ∀ p ∈ primeLogWindow H T,
      (∫ h in Ioc H T, (if Real.log p ≤ h then ((Real.log p : ℝ) : ℂ) else 0) * G' h)
        = ((Real.log p : ℝ) : ℂ) * (G T - G (Real.log p)) := by
    intro p hp
    have hlt := primeLogWindow_log_lt hp
    have hle := primeLogWindow_log_le hp
    refine integral_windowAtom_mul_deriv hlt hle ?_ ?_ _
    · intro x hx
      rw [Set.uIcc_of_le hle] at hx
      exact hG x ⟨le_trans hlt.le hx.1, hx.2⟩
    · exact hG'.mono_set (by
        rw [Set.uIcc_of_le hle, Set.uIcc_of_le hHT]
        exact Set.Icc_subset_Icc hlt.le le_rfl)
  have hsumint : (∫ h in Ioc H T,
      ((Chebyshev.theta (Real.exp h) - Chebyshev.theta (Real.exp H) : ℝ) : ℂ) * G' h)
      = ∑ p ∈ primeLogWindow H T,
          ∫ h in Ioc H T, (if Real.log p ≤ h then ((Real.log p : ℝ) : ℂ) else 0) * G' h := by
    rw [← MeasureTheory.integral_finsetSum _ hstep]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with h hh
    rw [← Finset.sum_mul, sum_primeLogWindow_indicatorC hh.1.le hh.2]
  have hmass : ∑ p ∈ primeLogWindow H T, ((Real.log p : ℝ) : ℂ)
      = ((Chebyshev.theta (Real.exp T) - Chebyshev.theta (Real.exp H) : ℝ) : ℂ) := by
    rw [← sum_primeLogWindow_indicatorC (H := H) (T := T) (h := T) hHT le_rfl]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [if_pos (primeLogWindow_log_le hp)]
  rw [intervalIntegral.integral_of_le hHT, hsumint, Finset.sum_congr rfl hpiece, ← hmass,
    Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

/-! ## The continuum pairing and the discrepancy form -/

theorem integral_mul_exp_byParts {G G' : ℝ → ℂ} {H T : ℝ} (hHT : H ≤ T)
    (hG : ∀ x ∈ Set.Icc H T, HasDerivAt G (G' x) x)
    (hG' : IntervalIntegrable G' volume H T) :
    (∫ h in H..T, G h * ((Real.exp h : ℝ) : ℂ))
      = G T * ((Real.exp T : ℝ) : ℂ) - G H * ((Real.exp H : ℝ) : ℂ)
        - ∫ h in H..T, G' h * ((Real.exp h : ℝ) : ℂ) := by
  have huIcc : Set.uIcc H T = Set.Icc H T := Set.uIcc_of_le hHT
  have hexp : ∀ x : ℝ, HasDerivAt (fun h : ℝ => ((Real.exp h : ℝ) : ℂ))
      ((Real.exp x : ℝ) : ℂ) x := fun x => (Real.hasDerivAt_exp x).ofReal_comp
  have hGcont : ContinuousOn G (Set.uIcc H T) := by
    rw [huIcc]
    intro x hx
    exact ((hG x hx).continuousAt).continuousWithinAt
  have hexpcont : ContinuousOn (fun h : ℝ => ((Real.exp h : ℝ) : ℂ)) (Set.uIcc H T) := by
    fun_prop
  have hF : ∀ x ∈ Set.uIcc H T,
      HasDerivAt (fun h : ℝ => G h * ((Real.exp h : ℝ) : ℂ))
        (G' x * ((Real.exp x : ℝ) : ℂ) + G x * ((Real.exp x : ℝ) : ℂ)) x := by
    intro x hx
    rw [huIcc] at hx
    exact (hG x hx).mul (hexp x)
  have hint1 : IntervalIntegrable (fun h : ℝ => G' h * ((Real.exp h : ℝ) : ℂ)) volume H T :=
    hG'.mul_continuousOn hexpcont
  have hint2 : IntervalIntegrable (fun h : ℝ => G h * ((Real.exp h : ℝ) : ℂ)) volume H T :=
    (hGcont.mul hexpcont).intervalIntegrable
  have hkey := intervalIntegral.integral_eq_sub_of_hasDerivAt hF (hint1.add hint2)
  rw [intervalIntegral.integral_add hint1 hint2] at hkey
  linear_combination hkey

/-- **The window quadrature defect in discrepancy form.** -/
theorem primeLogWindow_quadrature_eq {G G' : ℝ → ℂ} {H T : ℝ} (hHT : H ≤ T)
    (hG : ∀ x ∈ Set.Icc H T, HasDerivAt G (G' x) x)
    (hG' : IntervalIntegrable G' volume H T) :
    ∑ p ∈ primeLogWindow H T, ((Real.log p : ℝ) : ℂ) * G (Real.log p)
        - ∫ h in H..T, G h * ((Real.exp h : ℝ) : ℂ)
      = ((xiMassThetaLogDiscrepancy T : ℝ) : ℂ) * G T
        - ((xiMassThetaLogDiscrepancy H : ℝ) : ℂ) * G H
        - ∫ h in H..T, ((xiMassThetaLogDiscrepancy h : ℝ) : ℂ) * G' h := by
  have huIcc : Set.uIcc H T = Set.Icc H T := Set.uIcc_of_le hHT
  have hexpcont : ContinuousOn
      (fun h : ℝ => (((Real.exp h - Chebyshev.theta (Real.exp H)) : ℝ) : ℂ))
      (Set.uIcc H T) := by fun_prop
  have hintA : IntervalIntegrable
      (fun h : ℝ =>
        ((Chebyshev.theta (Real.exp h) - Chebyshev.theta (Real.exp H) : ℝ) : ℂ) * G' h)
      volume H T := intervalIntegrable_thetaWindowStep_mul hHT hG'
  have hintB : IntervalIntegrable
      (fun h : ℝ => (((Real.exp h - Chebyshev.theta (Real.exp H)) : ℝ) : ℂ) * G' h)
      volume H T := hG'.continuousOn_mul hexpcont
  have hsplit : ∀ h : ℝ, ((xiMassThetaLogDiscrepancy h : ℝ) : ℂ) * G' h
      = ((Chebyshev.theta (Real.exp h) - Chebyshev.theta (Real.exp H) : ℝ) : ℂ) * G' h
        - (((Real.exp h - Chebyshev.theta (Real.exp H)) : ℝ) : ℂ) * G' h := by
    intro h
    rw [xiMassThetaLogDiscrepancy]
    push_cast
    ring
  have hIntE : (∫ h in H..T, ((xiMassThetaLogDiscrepancy h : ℝ) : ℂ) * G' h)
      = (∫ h in H..T,
          ((Chebyshev.theta (Real.exp h) - Chebyshev.theta (Real.exp H) : ℝ) : ℂ) * G' h)
        - ∫ h in H..T, (((Real.exp h - Chebyshev.theta (Real.exp H)) : ℝ) : ℂ) * G' h := by
    simp only [hsplit]
    exact intervalIntegral.integral_sub hintA hintB
  have hintC : IntervalIntegrable (fun h : ℝ => G' h * ((Real.exp h : ℝ) : ℂ)) volume H T :=
    hG'.mul_continuousOn (by fun_prop)
  have hsplitB : (∫ h in H..T, (((Real.exp h - Chebyshev.theta (Real.exp H)) : ℝ) : ℂ) * G' h)
      = (∫ h in H..T, G' h * ((Real.exp h : ℝ) : ℂ))
        - ((Chebyshev.theta (Real.exp H) : ℝ) : ℂ) * (G T - G H) := by
    have hpt : ∀ h : ℝ, (((Real.exp h - Chebyshev.theta (Real.exp H)) : ℝ) : ℂ) * G' h
        = G' h * ((Real.exp h : ℝ) : ℂ)
          - ((Chebyshev.theta (Real.exp H) : ℝ) : ℂ) * G' h := by
      intro h
      push_cast
      ring
    simp only [hpt]
    rw [intervalIntegral.integral_sub hintC (hG'.const_mul _),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x hx => hG x (by rwa [huIcc] at hx)) hG']
  rw [sum_primeLogWindow_mul_eq hHT hG hG', integral_mul_exp_byParts hHT hG hG', hIntE, hsplitB,
    xiMassThetaLogDiscrepancy, xiMassThetaLogDiscrepancy]
  push_cast
  ring

end

end RHTower
