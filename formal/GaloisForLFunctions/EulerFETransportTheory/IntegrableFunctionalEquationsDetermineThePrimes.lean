import GaloisForLFunctions.EulerFETransportTheory.IntegrableDefectsForceIntegerSupport
import GaloisForLFunctions.ExactEventTheory.IntegerSupportForcesExactArithmetic

/-!
# Integrable functional-equation defects and rational-prime rigidity

The critical-line Hamburger identity gives the defective theta law. Reality of its pole
coefficient and integer support reduce the classification to exact arithmetic on the lattice.
-/

open Complex MeasureTheory Filter Topology Set
open GaloisForLFunctions.ArithmeticPositiveDuality RHTower.HamburgerStability
open GaloisForLFunctions.ExactEventTheory
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.FreqHamburger

noncomputable section
namespace GaloisForLFunctions.EulerFETransportTheory

/-- A finite uncompleted defect cannot carry an imaginary pole residue. -/
theorem measure_pole_real_of_integrable_theta_defect {ν : Measure ℝ}
    (hsupp : ν (Iio 1) = 0) (hmom : Integrable (fun u : ℝ => 1 / u ^ 2) ν)
    {β : ℂ} {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) (hgi : Integrable g)
    (hθ : ∀ x : ℝ, 0 < x → measureTheta ν x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta ν x⁻¹ +
        -β + β * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x) :
    (β.re : ℂ) = β := by
  have hreal (ε : ℝ) : (measureSeries ν (ε : ℂ)).im = 0 ∧
      (measureDual ν (ε : ℂ)).im = 0 := by
    have hs := congrArg Complex.im (measureSeries_conj ν (ε : ℂ))
    have hd := congrArg Complex.im (measureDual_conj ν (ε : ℂ))
    simp only [Complex.conj_ofReal, Complex.conj_im] at hs hd
    constructor <;> linarith
  have hlim := (Complex.continuous_im.tendsto _).comp
    (tendsto_mul_integrable_defectLaplace hgm hgb hgi 0)
  simp only [Complex.ofReal_zero, zero_mul, add_zero, Complex.zero_im] at hlim
  change Tendsto (fun ε : ℝ => ((ε : ℂ) * defectLaplace g (ε : ℂ)).im)
    (𝓝[>] 0) (𝓝 0) at hlim
  simp only [Complex.im_ofReal_mul] at hlim
  have hid : ∀ ε : ℝ, 0 < ε →
      ε * (defectLaplace g (ε : ℂ)).im = β.im / Real.pi - ε * β.im := by
    intro ε hε
    have hh := congrArg Complex.im
      (measureSeries_eq_of_theta_defect hsupp hmom hgm hgb hθ
        (show 0 < (ε : ℂ).re from hε))
    rw [show (Real.pi : ℂ) * (ε : ℂ) = ((Real.pi * ε : ℝ) : ℂ) by push_cast; rfl] at hh
    simp only [Complex.add_im, Complex.div_ofReal_im, Complex.neg_im,
      (hreal ε).1, (hreal ε).2, zero_add] at hh
    field_simp [Real.pi_ne_zero, ne_of_gt hε] at hh ⊢
    nlinarith only [hh]
  have hother : Tendsto (fun ε : ℝ => β.im / Real.pi - ε * β.im)
      (𝓝[>] 0) (𝓝 (β.im / Real.pi)) := by
    simpa using ((by fun_prop : Continuous fun ε : ℝ =>
      β.im / Real.pi - ε * β.im).tendsto 0).mono_left nhdsWithin_le_nhds
  have hzero : Tendsto (fun ε : ℝ => β.im / Real.pi - ε * β.im)
      (𝓝[>] 0) (𝓝 0) := by
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hid ε hε
  have hi := (div_eq_zero_iff.mp (tendsto_nhds_unique hother hzero)).resolve_right Real.pi_ne_zero
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im] using hi.symm

/-- The unit atom alone cannot satisfy the Riemann theta law with an integrable defect. -/
theorem beurling_labels_nonempty_of_integrable_theta_defect
    (B : RHTower.BeurlingSystem) [Countable B.Label]
    {β : ℝ} {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) (hgi : Integrable g)
    (hθ : ∀ x : ℝ, 0 < x → measureTheta (beurlingSystemIntegerMeasure B) x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta (beurlingSystemIntegerMeasure B) x⁻¹ +
        -(β : ℂ) + (β : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x) :
    Nonempty B.Label := by
  classical
  by_contra hempty
  have hx0 : ∀ x : B.Integer, x = 0 := by
    intro x
    induction x using Multiset.induction_on with
    | empty => rfl
    | cons l s ih => exact False.elim (hempty ⟨l⟩)
  let a : ℕ → ℝ := fun n => if n = 0 then 1 else 0
  let lam : ℕ → ℝ := fun n => (n : ℝ) + 1
  have ha0 : ∀ n, 0 ≤ a n := fun n => by simp only [a]; split_ifs <;> norm_num
  have hlam : ∀ n, 1 ≤ lam n := fun n => by
    dsimp only [lam]
    linarith only [Nat.cast_nonneg n (α := ℝ)]
  have hmono : StrictMono lam := by
    intro m n hmn
    change (m : ℝ) + 1 < (n : ℝ) + 1
    have hmnR : (m : ℝ) < (n : ℝ) := by exact_mod_cast hmn
    linarith only [hmnR]
  have ha : Summable fun n => a n / lam n ^ 2 := by
    apply summable_of_ne_finset_zero (s := {0})
    intro n hn
    simp only [Finset.mem_singleton] at hn
    simp [a, hn]
  have ht (x : ℝ) : measureTheta (beurlingSystemIntegerMeasure B) x =
      freqTheta (fun n => (a n : ℂ)) lam x := by
    rw [measureTheta_beurlingSystemIntegerMeasure]
    unfold beurlingTheta
    rw [tsum_eq_single (0 : B.Integer) (fun x hx => False.elim (hx (hx0 x)))]
    unfold freqTheta
    rw [tsum_eq_single 0 (fun n hn => by simp [a, hn])]
    simp [a, lam, B.intNorm_zero]
  have hθ' : ∀ x : ℝ, 0 < x → freqTheta (fun n => (a n : ℂ)) lam x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * freqTheta (fun n => (a n : ℂ)) lam x⁻¹ +
        -(β : ℂ) + (β : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x := by
    intro x hx
    simpa only [ht] using hθ x hx
  have hpole := integer_support_pins_pole_residue hmono (by simp [lam])
    (fun n => ⟨n + 1, by simp [lam]⟩) ha0 ha hgm hgb hgi hθ'
  have hres := tendsto_mul_freqDual_zero_of_theta_defect ha0 hlam ha hgm hgb hgi hθ'
  have hd (ε : ℝ) : freqDual (fun n => (a n : ℂ)) lam (ε : ℂ) =
      Complex.exp (-(2 * Real.pi * (ε : ℂ))) := by
    unfold freqDual
    rw [tsum_eq_single 0 (fun n hn => by simp [a, hn])]
    simp [a, lam]
  have hz : Tendsto (fun ε : ℝ => (ε : ℂ) *
      freqDual (fun n => (a n : ℂ)) lam (ε : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    simp only [hd]
    have hc : Continuous fun ε : ℝ => (ε : ℂ) * Complex.exp (-(2 * Real.pi * (ε : ℂ))) :=
      by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hb : (β : ℂ) = 0 := (div_eq_zero_iff.mp (tendsto_nhds_unique hres hz)).resolve_right
    (by exact_mod_cast Real.pi_ne_zero)
  have hb' : β = 0 := by exact_mod_cast hb
  simp [a, hb'] at hpole

/-- In the Hamburger strip class, every integrable uncompleted FE defect forces precisely
the rational-prime system. No norm lattice, nonempty-label or defect-size premise is needed. -/
theorem beurlingSystem_rigidity_of_integrable_defect
    (B : RHTower.BeurlingSystem) [Countable B.Label]
    (hBsum : Summable fun x : B.Integer => B.intNorm x ^ (-(3 / 2 : ℝ)))
    {E : ℂ → ℂ} {β : ℂ} {C : ℝ} {g : ℝ → ℂ} {Cg : ℝ} {Ng : ℕ}
    (hEc : ContinuousOn E (verticalStrip (1 / 2) (3 / 2)))
    (hEd : DifferentiableOn ℂ E {s : ℂ | 1 / 2 < s.re ∧ s.re < 3 / 2})
    (hdecay : ∀ s ∈ verticalStrip (1 / 2) (3 / 2), ‖E s‖ ≤ C / (1 + s.im ^ 2))
    (hR : ∀ s : ℂ, s.re = 3 / 2 →
      Complex.Gammaℝ s * beurlingZeta B s = E s + β * Complex.Gammaℝ (s - 1))
    (hC : ∀ s : ℂ, s.re = 1 / 2 → E s - E (1 - s) =
      -(β * (Complex.Gammaℝ (s - 1) - Complex.Gammaℝ (-s))) + Complex.Gammaℝ s * g (s.im / 2))
    (hgm : Measurable g) (hgb : ∀ t : ℝ, ‖g t‖ ≤ Cg * (1 + |t|) ^ Ng) (hgi : Integrable g) :
    β = 1 / 2 ∧
      beurlingSystemIntegerMeasure B = beurlingIntegerMeasure riemannPrimeMeasure ∧
      (∀ x : B.Integer, ∃ m : ℕ, 1 ≤ m ∧ B.intNorm x = (m : ℝ)) ∧
      (∀ m : ℕ, 1 ≤ m → ∃! x : B.Integer, B.intNorm x = (m : ℝ)) ∧
      (∀ s : ℂ, 1 < s.re → beurlingZeta B s = riemannZeta s) ∧
      Nonempty {e : B.Label ≃ {p : ℕ // Nat.Prime p} //
        ∀ l : B.Label, B.labelNorm l = ((e l : ℕ) : ℝ)} := by
  have hsupp := beurlingSystemIntegerMeasure_Iio_one_eq_zero B
  have hmom := integrable_rpow_beurlingSystemIntegerMeasure B hBsum
  have hR' : ∀ s : ℂ, s.re = 3 / 2 →
      Complex.Gammaℝ s * measureDirichlet (beurlingSystemIntegerMeasure B) s =
        E s + β * Complex.Gammaℝ (s - 1) := by
    simpa only [measureDirichlet_beurlingSystemIntegerMeasure] using hR
  have hθ := measureTheta_defect_relation hsupp hmom hEc hEd hdecay hR' hC hgm hgb
  have hβ := measure_pole_real_of_integrable_theta_defect hsupp
    (integrable_inv_sq_of_integrable_rpow_neg_three_halves hsupp hmom) hgm hgb hgi hθ
  have hθreal : ∀ x : ℝ, 0 < x → measureTheta (beurlingSystemIntegerMeasure B) x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta (beurlingSystemIntegerMeasure B) x⁻¹ +
        -(β.re : ℂ) + (β.re : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x := by
    simpa only [hβ] using hθ
  haveI := beurling_labels_nonempty_of_integrable_theta_defect B hgm hgb hgi hθreal
  have hint := beurling_intNorm_nat_of_integrable_theta_defect B hBsum hgm hgb hgi hθreal
  exact beurlingSystem_rigidity_of_integer_support_integrable_defect B hint hBsum
    hEc hEd hdecay hR hC hgm hgb hgi

/-- Every nonclassical system in the same analytic class has infinite uncompleted defect
cost. This also excludes every nonclassical finite-layer candidate at finite cost. -/
theorem nonclassical_beurling_defect_cost_eq_top
    (B : RHTower.BeurlingSystem) [Countable B.Label]
    (hBsum : Summable fun x : B.Integer => B.intNorm x ^ (-(3 / 2 : ℝ)))
    {E : ℂ → ℂ} {β : ℂ} {C : ℝ} {g : ℝ → ℂ} {Cg : ℝ} {Ng : ℕ}
    (hEc : ContinuousOn E (verticalStrip (1 / 2) (3 / 2)))
    (hEd : DifferentiableOn ℂ E {s : ℂ | 1 / 2 < s.re ∧ s.re < 3 / 2})
    (hdecay : ∀ s ∈ verticalStrip (1 / 2) (3 / 2), ‖E s‖ ≤ C / (1 + s.im ^ 2))
    (hR : ∀ s : ℂ, s.re = 3 / 2 →
      Complex.Gammaℝ s * beurlingZeta B s = E s + β * Complex.Gammaℝ (s - 1))
    (hC : ∀ s : ℂ, s.re = 1 / 2 → E s - E (1 - s) =
      -(β * (Complex.Gammaℝ (s - 1) - Complex.Gammaℝ (-s))) + Complex.Gammaℝ s * g (s.im / 2))
    (hgm : Measurable g) (hgb : ∀ t : ℝ, ‖g t‖ ≤ Cg * (1 + |t|) ^ Ng)
    (hnonclassical : ¬ Nonempty {e : B.Label ≃ {p : ℕ // Nat.Prime p} //
      ∀ l : B.Label, B.labelNorm l = ((e l : ℕ) : ℝ)}) :
    (∫⁻ t : ℝ, ‖g t‖ₑ) = ⊤ := by
  by_contra hcost
  have hgi : Integrable g := ⟨hgm.aestronglyMeasurable, lt_top_iff_ne_top.mpr hcost⟩
  obtain ⟨_, _, _, _, _, hprimes⟩ := beurlingSystem_rigidity_of_integrable_defect B hBsum
    hEc hEd hdecay hR hC hgm hgb hgi
  exact hnonclassical hprimes

end GaloisForLFunctions.EulerFETransportTheory

#print axioms GaloisForLFunctions.EulerFETransportTheory.measure_pole_real_of_integrable_theta_defect
#print axioms GaloisForLFunctions.EulerFETransportTheory.beurling_labels_nonempty_of_integrable_theta_defect
#print axioms GaloisForLFunctions.EulerFETransportTheory.beurlingSystem_rigidity_of_integrable_defect

#print axioms GaloisForLFunctions.EulerFETransportTheory.nonclassical_beurling_defect_cost_eq_top
