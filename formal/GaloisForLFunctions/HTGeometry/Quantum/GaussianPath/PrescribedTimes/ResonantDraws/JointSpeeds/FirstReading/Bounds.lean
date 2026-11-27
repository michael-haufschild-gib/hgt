import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.JointSpeeds.FirstExcursionLaw
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.FirstPassageSelection.PhaseWeights.OccupationBounds

/-! # Sample counts for a first affordable reading after the original excursion -/
open Set MeasureTheory ProbabilityTheory Filter Topology
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.JointSpeeds
open ResonantDraws SharpOccupation
noncomputable section
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩

private theorem miss_bounds {l p b : ℝ} (hp : p∈Icc (0:ℝ) 1) (hl : l≤p) (hb : p≤b) (q : ℕ) :
    1-(q:ℝ)*b ≤ (1-p)^q ∧ (1-p)^q ≤ Real.exp (-((q:ℝ)*l)) := by
  constructor
  · have h := one_add_mul_le_pow (a:=-p) (by linarith [hp.2]) q
    rw [←sub_eq_add_neg,mul_neg,←sub_eq_add_neg] at h
    exact (sub_le_sub_left (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg q)) 1).trans h
  · have h : 1-p ≤ Real.exp (-l) := by
      linarith only [hl,Real.add_one_le_exp (-l)]
    calc (1-p)^q ≤ (Real.exp (-l))^q := pow_le_pow_left₀ (sub_nonneg.mpr hp.2) h q
         _ = _ := by rw [←Real.exp_nat_mul,mul_neg]

/-- With q incommensurate observations, the limiting miss probability,
conditional on any selection of prefixes, lies between 1-q b^D and
exp(-q l^D). The size cutoff is uniform in the selection and q. -/
theorem subcritical_first_reading_bounds (s : ℕ→ℕ) (hs : subcriticalBudget s)
    {ε : ℝ} (hε : ε∈Ioo (0:ℝ) (Real.sqrt 2)) {l b : ℝ}
    (hl : 0≤l) (hlx : l<physicalArc ε) (hxb : physicalArc ε<b) :
    ∀ᶠ k : ℕ in atTop, let n := k+1
      let K := k+3
      let D := 2^K
      let P := nearHilbertContinuousCircuitBudget K
      let μ := Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1
      let σ := crossingOrigin n P (9/80)
      ∀ (I : Type) [Fintype I] (c : I→ℝ), RationallyIndependentFrequency c →
        ∀ (r j : ℕ), j ≤ s K → ∀ (afterReturn : Bool) (B : Set (PrefixIndex n→ℝ)), MeasurableSet B →
          let o := fun x => if afterReturn then σ x+crossingWait n P r x else σ x
          let q : ℝ := Fintype.card I
          ∃ a : ℝ, μ.real B*(1-q*b^D)≤a ∧ a≤μ.real B*Real.exp (-(q*l^D)) ∧
            Tendsto (fun t => μ.real (B ∩ {x | ∀ i, ε<pathGateDistance n j x (o x+c i*t)})) atTop (𝓝 a) := by
  classical
  filter_upwards [subcritical_phase_mass s hs hε hl hlx hxb] with k hk
  intro n K D P μ σ I _ c hc r j hj afterReturn B hB o q
  let X := fun (ω : PathPauliDisorder) i => pathPauliDisorderShell ω n (pathCoeffEquiv n i)
  let A := X ⁻¹' B
  let W := affordablePhaseMass k j ε
  let m := Fintype.card I
  letI : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance
  have hw (ω) : W ω∈Icc (0:ℝ) 1 := ⟨measureReal_nonneg,measureReal_le_one⟩
  have hint : Integrable (fun ω => (1-W ω)^m) (pathPauliDisorderLaw.restrict A) := by
    have hW : Integrable W (pathPauliDisorderLaw.restrict A) := (integrable_affordablePhaseMass k j ε).integrableOn
    refine Integrable.of_bound ((aestronglyMeasurable_const.sub hW.aestronglyMeasurable).pow m) 1 ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (sub_nonneg.mpr (hw ω).2) m)]
    exact pow_le_one₀ (sub_nonneg.mpr (hw ω).2) (sub_le_self _ (hw ω).1)
  have hbd : ∀ᵐ ω ∂(pathPauliDisorderLaw.restrict A),
      1-q*b^D ≤ (1-W ω)^m ∧ (1-W ω)^m ≤ Real.exp (-(q*l^D)) :=
    ae_restrict_of_ae (hk.mono fun ω h => miss_bounds (hw ω) (h j hj).1 (h j hj).2 m)
  have hmass : pathPauliDisorderLaw.real A=μ.real B :=
    (gaussian_pauli_prefix_coordinates_law n).measureReal_preimage hB.nullMeasurableSet
  have hlo := integral_mono_ae (integrable_const (1-q*b^D)) hint (hbd.mono fun _ h => h.1)
  have hhi := integral_mono_ae hint (integrable_const (Real.exp (-(q*l^D)))) (hbd.mono fun _ h => h.2)
  rw [setIntegral_const,smul_eq_mul,hmass] at hlo hhi
  refine ⟨_,hlo,hhi,?_⟩
  have ht := joint_first_excursion_snapshot k P c hc (fun _ => afterReturn) (fun _ => false)
    (fun _ => r) (fun _ => j) (fun _ => ε) B hB
  simpa only [Bool.false_eq_true,iff_false,not_le,if_false,Finset.prod_const,Finset.card_univ] using ht

#print axioms subcritical_first_reading_bounds
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.JointSpeeds
