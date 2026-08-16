import GaloisForLFunctions.HTGeometry.StabilizerPureState
import GaloisForLFunctions.HTGeometry.CircuitCountingCollisionBound

/-!
# Markov and circuit counting at the two-design collision scale

A nonnegative quantity with a known total exceeds a threshold on a proportionally small part of a
finite index set.  Applied to the stabilizer collision, whose total is fixed by the two-design law,
this bounds the fraction of stabilizer states whose collision exceeds `2L/(D+1)` by `1/L`.  At a
replica order below the reciprocal of that collision scale the complete-target capture bound becomes
`2^{-r/2}` above the return density.
-/

open Finset MeasureTheory

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

section Markov

/-- **Markov's inequality on a finite index set.** -/
theorem finite_markov {ι : Type*} [DecidableEq ι] (T : Finset ι) (g : ι → ℝ)
    (hg : ∀ i ∈ T, 0 ≤ g i) (t : ℝ) :
    ((T.filter fun i => t < g i).card : ℝ) * t ≤ ∑ i ∈ T, g i := by
  classical
  have hsub : (T.filter fun i => t < g i) ⊆ T := Finset.filter_subset _ _
  have hlow : ((T.filter fun i => t < g i).card : ℝ) * t ≤
      ∑ i ∈ T.filter fun i => t < g i, g i := by
    calc ((T.filter fun i => t < g i).card : ℝ) * t
        = ∑ _i ∈ T.filter fun i => t < g i, t := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ T.filter fun i => t < g i, g i := by
          refine Finset.sum_le_sum fun i hi => ?_
          exact le_of_lt (Finset.mem_filter.mp hi).2
  refine le_trans hlow ?_
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun i hi _ => hg i hi

end Markov

section StabilizerMarkov

variable {n : ℕ}

/-- **The Markov form of the two-design collision law.**  At most a fraction `1/L` of the stabilizer
states have collision above `2L/(D+1)`. -/
theorem card_filter_collision_gt_mul_le
    (e : FiniteQubitConfiguration (Fin n) → FiniteQubitConfiguration (Fin n) → ℂ)
    (χ : (Fin n → PauliSymp n) → (Fin n → ZMod 2) → (FiniteQubitConfiguration (Fin n) → ℂ))
    (hsum : ((2 : ℝ) ^ n + 1) * (∑ b ∈ lagrBases n, ∑ ε : Fin n → ZMod 2,
        ∑ j, (finitePureStateFidelity (e j) (χ b ε)) ^ 2) =
      ((lagrBases n).card : ℝ) * 2 ^ (n + 1))
    (L : ℝ) :
    ((((lagrBases n) ×ˢ (Finset.univ : Finset (Fin n → ZMod 2))).filter fun q =>
        2 * L < ((2 : ℝ) ^ n + 1) *
          ∑ j, (finitePureStateFidelity (e j) (χ q.1 q.2)) ^ 2).card : ℝ) * L ≤
      ((lagrBases n).card : ℝ) * 2 ^ n := by
  classical
  set g : ((Fin n → PauliSymp n) × (Fin n → ZMod 2)) → ℝ := fun q =>
    ((2 : ℝ) ^ n + 1) * ∑ j, (finitePureStateFidelity (e j) (χ q.1 q.2)) ^ 2 with hgdef
  have hgnonneg : ∀ q ∈ (lagrBases n) ×ˢ (Finset.univ : Finset (Fin n → ZMod 2)), 0 ≤ g q := by
    intro q _
    rw [hgdef]
    have hpos : (0 : ℝ) ≤ (2 : ℝ) ^ n + 1 := by positivity
    have hsq : (0 : ℝ) ≤ ∑ j, (finitePureStateFidelity (e j) (χ q.1 q.2)) ^ 2 :=
      Finset.sum_nonneg fun j _ => sq_nonneg _
    exact mul_nonneg hpos hsq
  have htotal : (∑ q ∈ (lagrBases n) ×ˢ (Finset.univ : Finset (Fin n → ZMod 2)), g q) =
      ((lagrBases n).card : ℝ) * 2 ^ (n + 1) := by
    rw [Finset.sum_product]
    calc (∑ b ∈ lagrBases n, ∑ ε : Fin n → ZMod 2, g (b, ε))
        = ((2 : ℝ) ^ n + 1) * ∑ b ∈ lagrBases n, ∑ ε : Fin n → ZMod 2,
            ∑ j, (finitePureStateFidelity (e j) (χ b ε)) ^ 2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.mul_sum]
      _ = ((lagrBases n).card : ℝ) * 2 ^ (n + 1) := hsum
  have hmarkov := finite_markov ((lagrBases n) ×ˢ (Finset.univ : Finset (Fin n → ZMod 2))) g
    hgnonneg (2 * L)
  rw [htotal] at hmarkov
  have hpow : (2 : ℝ) ^ (n + 1) = 2 ^ n * 2 := by ring
  rw [hpow] at hmarkov
  nlinarith [hmarkov]

end StabilizerMarkov

section CircuitCounting

variable {d : Type*} [Fintype d] [DecidableEq d]
variable {C : Type*} [Fintype C] [Nonempty C]

/-- **The complete-target capture bound at the two-design collision scale.** -/
theorem measureReal_capture_le_return_add_two_rpow_of_design
    {p : d → ℝ} (hp : ∀ j, 0 ≤ p j) (hpsum : ∑ j, p j ≤ 1) {a : ℝ} (ha : 0 < a)
    (z : C → (d → ℂ)) (hz : ∀ c, finiteComplexInner (z c) (z c) = 1)
    (hznorm : ∀ c, ∑ j, ‖z c j‖ ^ 2 ≤ 1)
    {R Q : Set (d → ℝ)} (hR : MeasurableSet R)
    (hcap : ∀ x ∈ Q \ R, ∃ c, a ≤ finitePureStateFidelity (torusReplicaPhaseOrbit p x) (z c))
    {r : ℕ} (hr : 1 ≤ r) {L D1 : ℝ} (hL : 0 < L) (hD1 : 0 < D1)
    (hcoll : occupationCollision p ≤ 2 * L / D1)
    (hrle : (r : ℝ) ≤ a ^ 2 * D1 / (64 * L))
    {M : ℝ} (hM : 1 < M) {s : ℕ} (hcard : (Fintype.card C : ℝ) ≤ M ^ (s + 1))
    (hs : ((s : ℝ) + 1) * Real.log M ≤ ((r : ℝ) / 2) * Real.log 2) :
    (volume.restrict (torusBox d)).real Q ≤
      (volume.restrict (torusBox d)).real R + (2 : ℝ) ^ (-((r : ℝ) / 2)) := by
  have hc₀ : (0 : ℝ) ≤ 2 * L / D1 := by positivity
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  have hscale : 16 * (2 * L / D1) / a ^ 2 ≤ 1 / (2 * r) := by
    have heq : 16 * (2 * L / D1) / a ^ 2 = (32 * L) / (D1 * a ^ 2) := by
      field_simp
      ring
    rw [heq, div_le_div_iff₀ (by positivity) (by positivity)]
    have hfrom : (r : ℝ) * (64 * L) ≤ a ^ 2 * D1 := by
      rw [le_div_iff₀ (by positivity)] at hrle
      linarith [hrle]
    nlinarith [hfrom]
  exact measureReal_capture_le_return_add_two_rpow hp hpsum ha z hz hznorm hR hcap hr hc₀ hcoll
    hscale hM hcard hs

end CircuitCounting

end GaloisForLFunctions.HTGeometry
