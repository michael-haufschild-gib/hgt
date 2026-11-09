import GaloisForLFunctions.EulerFETransportTheory.FiniteEnergyDefectsForceIntegerSupport
import GaloisForLFunctions.EulerFETransportTheory.FiniteEnergyDefectsPreserveAtomicResidues

/-!
# Finite-energy functional equations determine the rational primes

The actual theta identity forces integer support and fixes all atomic multiplicities.
The resulting counting measure identifies the generalized integers and their prime
generators. The Hamburger strip formulation supplies the theta identity directly.
-/

open Complex MeasureTheory Filter Topology Set
open GaloisForLFunctions.ArithmeticPositiveDuality RHTower.HamburgerStability
open GaloisForLFunctions.ExactEventTheory
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.FreqHamburger

noncomputable section
namespace GaloisForLFunctions.EulerFETransportTheory

/-- The unit atom alone cannot satisfy the actual theta law with a finite-energy defect. -/
theorem beurling_labels_nonempty_of_finiteEnergy_theta_defect
    (B : RHTower.BeurlingSystem) [Countable B.Label]
    {β : ℝ} {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) (hg : MemLp g 2 (volume : Measure ℝ))
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
  have hpole := finiteEnergy_integer_support_pins_pole_residue hmono (by simp [lam])
    (fun n => ⟨n + 1, by simp [lam]⟩) ha0 ha hgm hgb hg hθ'
  have hres := tendsto_mul_freqDual_zero_of_finiteEnergy_theta_defect ha0 hlam ha hgm hgb hg hθ'
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

/-- The actual theta law with any finite-energy defect determines the complete Beurling
system. Integer support, unit density and unique norm factorization are conclusions. -/
theorem beurlingSystem_rigidity_of_finiteEnergy_theta_defect
    (B : RHTower.BeurlingSystem) [Countable B.Label]
    (hBsum : Summable fun i : B.Integer => B.intNorm i ^ (-(3 / 2 : ℝ)))
    {β : ℝ} {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) (hg : MemLp g 2 (volume : Measure ℝ))
    (hθ : ∀ x : ℝ, 0 < x → measureTheta (beurlingSystemIntegerMeasure B) x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta (beurlingSystemIntegerMeasure B) x⁻¹ +
        -(β : ℂ) + (β : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x) :
    β = 1 / 2 ∧
      beurlingSystemIntegerMeasure B = beurlingIntegerMeasure riemannPrimeMeasure ∧
      (∀ x : B.Integer, ∃ m : ℕ, 1 ≤ m ∧ B.intNorm x = (m : ℝ)) ∧
      (∀ m : ℕ, 1 ≤ m → ∃! x : B.Integer, B.intNorm x = (m : ℝ)) ∧
      (∀ s : ℂ, 1 < s.re → beurlingZeta B s = riemannZeta s) ∧
      Nonempty {e : B.Label ≃ {p : ℕ // Nat.Prime p} //
        ∀ l : B.Label, B.labelNorm l = ((e l : ℕ) : ℝ)} := by
  classical
  haveI := beurling_labels_nonempty_of_finiteEnergy_theta_defect B hgm hgb hg hθ
  have hint := beurling_intNorm_nat_of_finiteEnergy_theta_defect B hBsum hgm hgb hg hθ
  obtain ⟨lam, index, hmono, hlam0, hsurj, hnorm, hfinite⟩ := exists_ordered_beurling_norms B hBsum
  let A : ℕ → ℕ := fun n => Nat.card {x : B.Integer // index x = n}
  have hA1 : ∀ n, 1 ≤ A n := by
    intro n
    letI : Fintype {x : B.Integer // index x = n} := (hfinite n).fintype
    obtain ⟨x, hx⟩ := hsurj n
    letI : Nonempty {x : B.Integer // index x = n} := ⟨⟨x, hx⟩⟩
    have hh : 0 < Fintype.card {x : B.Integer // index x = n} := Fintype.card_pos_iff.mpr inferInstance
    simp only [A, Nat.card_eq_fintype_card]
    omega
  have hunit0 : A 0 = 1 := by
    have hindex0 : index 0 = 0 := hmono.injective ((hnorm 0).trans B.intNorm_zero |>.trans hlam0.symm)
    apply Nat.card_eq_one_iff_exists.mpr
    refine ⟨⟨0, hindex0⟩, fun x => ?_⟩
    apply Subtype.ext
    exact (intNorm_eq_one_iff B x.val).mp (by rw [← hnorm x.val, x.property, hlam0])
  have hlamInt : ∀ n, ∃ k : ℕ, lam n = k := by
    intro n
    obtain ⟨x, hx⟩ := hsurj n
    obtain ⟨k, hk⟩ := hint x
    exact ⟨k, by rw [← hx, hnorm x, hk]⟩
  have hBsum2 := summable_beurling_inv_sq B hBsum
  have ha : Summable fun n => (A n : ℝ) / lam n ^ 2 := by
    have hh := (sum_by_ordered_norm_fibers hnorm hfinite (fun u => 1 / u ^ 2) hBsum2).1
    simpa only [nsmul_eq_mul, mul_one_div, A] using hh
  have htheta : ∀ x : ℝ, 0 < x →
      measureTheta (beurlingSystemIntegerMeasure B) x =
        freqTheta (fun n => ((A n : ℝ) : ℂ)) lam x := by
    intro x hx
    rw [measureTheta_beurlingSystemIntegerMeasure]
    have hs : Summable fun y : B.Integer => ((Real.exp (-Real.pi * B.intNorm y ^ 2 * x) : ℝ) : ℂ) := by
      refine Summable.of_norm_bounded (hBsum2.mul_left ((Real.pi * x)⁻¹)) fun y => ?_
      simpa only [one_mul, norm_one] using norm_thetaTerm_le
        (a := fun _ => (1 : ℂ)) (lam := fun _ => B.intNorm y) (fun _ => B.one_le_intNorm y) hx 0
    have hh := (sum_by_ordered_norm_fibers hnorm hfinite
      (fun u => ((Real.exp (-Real.pi * u ^ 2 * x) : ℝ) : ℂ)) hs).2
    simpa only [beurlingTheta, freqTheta, nsmul_eq_mul, Complex.ofReal_natCast, A] using hh
  have hθfreq : ∀ x : ℝ, 0 < x → freqTheta (fun n => ((A n : ℝ) : ℂ)) lam x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * freqTheta (fun n => ((A n : ℝ) : ℂ)) lam x⁻¹ +
        -(β : ℂ) + (β : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x := by
    intro x hx
    simpa only [htheta x hx, htheta x⁻¹ (inv_pos.mpr hx)] using hθ x hx
  obtain ⟨hβ, hvals⟩ := integer_spectrum_of_integer_support_finiteEnergy_defect
    hmono hlam0 hlamInt (fun n => by exact_mod_cast hA1 n)
    (by exact_mod_cast hunit0) ha hgm hgb hg hθfreq
  have hnormnat : ∀ x : B.Integer, B.intNorm x = (index x : ℝ) + 1 :=
    fun x => (hnorm x).symm.trans (hvals (index x)).1
  have hinj : Function.Injective index := by
    intro x y hxy
    letI : Fintype {z : B.Integer // index z = index x} := (hfinite (index x)).fintype
    have hc : Fintype.card {z : B.Integer // index z = index x} ≤ 1 := by
      rw [← Nat.card_eq_fintype_card]
      exact_mod_cast (hvals (index x)).2.le
    letI := Fintype.card_le_one_iff_subsingleton.mp hc
    exact congrArg Subtype.val (Subsingleton.elim
      (⟨x, rfl⟩ : {z : B.Integer // index z = index x}) ⟨y, hxy.symm⟩)
  let e : B.Integer ≃ ℕ := Equiv.ofBijective index ⟨hinj, hsurj⟩
  have hν : beurlingSystemIntegerMeasure B =
      Measure.sum (fun k : ℕ => Measure.dirac ((k : ℝ) + 1)) := by
    ext s hs
    rw [beurlingSystemIntegerMeasure, Measure.sum_apply _ hs, Measure.sum_apply _ hs]
    simp only [hnormnat]
    exact e.tsum_eq (fun n => Measure.dirac ((n : ℝ) + 1) s)
  exact ⟨hβ, beurlingSystem_rigidity_of_integer_measure_eq B hν⟩

/-- In the Hamburger strip class, square integrability of the uncompleted defect
forces precisely the rational primes, with no lattice or defect-size premise. -/
theorem beurlingSystem_rigidity_of_finiteEnergy_defect
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
    (hg : MemLp g 2 (volume : Measure ℝ)) :
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
  have hβ := measure_pole_real_of_finiteEnergy_theta_defect hsupp
    (integrable_inv_sq_of_integrable_rpow_neg_three_halves hsupp hmom) hgm hgb hg hθ
  have hθreal : ∀ x : ℝ, 0 < x → measureTheta (beurlingSystemIntegerMeasure B) x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta (beurlingSystemIntegerMeasure B) x⁻¹ +
        -(β.re : ℂ) + (β.re : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x := by
    simpa only [hβ] using hθ
  obtain ⟨hb, hrest⟩ := beurlingSystem_rigidity_of_finiteEnergy_theta_defect B hBsum hgm hgb hg hθreal
  refine ⟨?_, hrest⟩
  rw [← hβ, hb]
  norm_num

/-- Every nonclassical system in the same Hamburger strip class has infinite
uncompleted defect energy. -/
theorem nonclassical_beurling_defect_energy_eq_top
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
    (∫⁻ t : ℝ, ‖g t‖ₑ ^ (2 : ℕ)) = ⊤ := by
  by_contra henergy
  have hg : MemLp g 2 (volume : Measure ℝ) := by
    refine ⟨hgm.aestronglyMeasurable, ?_⟩
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    norm_num only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) henergy
  obtain ⟨_, _, _, _, _, hprimes⟩ := beurlingSystem_rigidity_of_finiteEnergy_defect B hBsum
    hEc hEd hdecay hR hC hgm hgb hg
  exact hnonclassical hprimes

end GaloisForLFunctions.EulerFETransportTheory

#print axioms GaloisForLFunctions.EulerFETransportTheory.beurling_labels_nonempty_of_finiteEnergy_theta_defect
#print axioms GaloisForLFunctions.EulerFETransportTheory.beurlingSystem_rigidity_of_finiteEnergy_theta_defect
#print axioms GaloisForLFunctions.EulerFETransportTheory.beurlingSystem_rigidity_of_finiteEnergy_defect
#print axioms GaloisForLFunctions.EulerFETransportTheory.nonclassical_beurling_defect_energy_eq_top
