import GaloisForLFunctions.ArithmeticPositiveDuality.IntegralSpectraHaveAPoleResidueGap
import GaloisForLFunctions.ArithmeticPositiveDuality.SmallDefectsBoundThePoleResidue
import GaloisForLFunctions.ArithmeticPositiveDuality.BeurlingNormsHaveAnOrderedIntegralSpectrum

/-!
# Small integrable functional-equation defects force the rational primes

An uncompleted defect of L¹ norm at most 1/6400 gives residue at most 19/16. Integer multiplicities
and three-point positivity exclude every residue between 1 and √2. The spectrum is therefore the
positive integers with unit masses, and its multiplicative generators are the rational primes.
-/

open Complex MeasureTheory Filter Topology Set
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.FreqHamburger
open RHTower.HamburgerStability

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositiveDuality

/-- A uniformly small integrable uncompleted FE defect forces exact categorical arithmetic rigidity. -/
theorem beurlingSystem_rigidity_of_small_critical_line_defect
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
    (hgm : Measurable g) (hgb : ∀ t : ℝ, ‖g t‖ ≤ Cg * (1 + |t|) ^ Ng) (hgi : Integrable g)
    (hsmall : 6400 * ∫ t, ‖g t‖ ≤ 1) :
    β = 1 / 2 ∧
      beurlingSystemIntegerMeasure B = beurlingIntegerMeasure riemannPrimeMeasure ∧
      (∀ x : B.Integer, ∃ m : ℕ, 1 ≤ m ∧ B.intNorm x = (m : ℝ)) ∧
      (∀ m : ℕ, 1 ≤ m → ∃! x : B.Integer, B.intNorm x = (m : ℝ)) ∧
      (∀ s : ℂ, 1 < s.re → beurlingZeta B s = riemannZeta s) ∧
      Nonempty {e : B.Label ≃ {p : ℕ // Nat.Prime p} //
        ∀ l : B.Label, B.labelNorm l = ((e l : ℕ) : ℝ)} := by
  classical
  have hsmall4 : 400 * (4 : ℝ) ^ 2 * ∫ t, ‖g t‖ ≤ 1 := by
    convert hsmall using 1 <;> norm_num
  obtain ⟨-, hU, -⟩ := beurling_primes_of_critical_line_defect B hBsum hEc hEd hdecay hR hC
    hgm hgb hgi (N := 4) (by omega) hsmall4
  obtain ⟨x₂, hx₂, -⟩ := hU 2 (by omega) (by omega)
  have hx₂0 : x₂ ≠ 0 := by intro h; subst x₂; norm_num [B.intNorm_zero] at hx₂
  obtain ⟨p, -⟩ := Multiset.exists_mem_of_ne_zero hx₂0
  letI : Nonempty B.Label := ⟨p⟩
  obtain ⟨lam, index, hmono, hlam0, hsurj, hnorm, hfinite⟩ := exists_ordered_beurling_norms B hBsum
  let A : ℕ → ℕ := fun n => Nat.card {x : B.Integer // index x = n}
  have hA1 : ∀ n, 1 ≤ A n := by
    intro n
    letI := (hfinite n).fintype
    obtain ⟨x, hx⟩ := hsurj n
    letI : Nonempty {x : B.Integer // index x = n} := ⟨⟨x, hx⟩⟩
    have hh : 0 < Fintype.card {x : B.Integer // index x = n} := Fintype.card_pos_iff.mpr inferInstance
    simpa only [A, Nat.card_eq_fintype_card] using hh
  have hlam : ∀ n, 1 ≤ lam n := fun n => hlam0 ▸ hmono.monotone (Nat.zero_le n)
  have ha0 : ∀ n, 0 ≤ (A n : ℝ) := fun _ => Nat.cast_nonneg _
  have hBsum2 : Summable fun x : B.Integer => 1 / B.intNorm x ^ 2 := by
    refine hBsum.of_nonneg_of_le (fun x => by positivity) fun x => ?_
    have hu := (B.intNorm_pos x).le
    rw [one_div, ← Real.rpow_natCast, ← Real.rpow_neg hu]
    exact Real.rpow_le_rpow_of_exponent_le (B.one_le_intNorm x) (by norm_num)
  have ha : Summable fun n => (A n : ℝ) / lam n ^ 2 := by
    have hh := (sum_by_ordered_norm_fibers hnorm hfinite (fun u => 1 / u ^ 2) hBsum2).1
    simpa only [nsmul_eq_mul, mul_one_div, A] using hh
  have htheta : ∀ x : ℝ, 0 < x →
      beurlingTheta B x = freqTheta (fun n => ((A n : ℝ) : ℂ)) lam x := by
    intro x hx
    have hs : Summable fun y : B.Integer => ((Real.exp (-Real.pi * B.intNorm y ^ 2 * x) : ℝ) : ℂ) := by
      refine Summable.of_norm_bounded (hBsum2.mul_left ((Real.pi * x)⁻¹)) fun y => ?_
      simpa only [one_mul, norm_one] using norm_thetaTerm_le
        (a := fun _ => (1 : ℂ)) (lam := fun _ => B.intNorm y) (fun _ => B.one_le_intNorm y) hx 0
    have hh := (sum_by_ordered_norm_fibers hnorm hfinite
      (fun u => ((Real.exp (-Real.pi * u ^ 2 * x) : ℝ) : ℂ)) hs).2
    simpa only [beurlingTheta, freqTheta, nsmul_eq_mul, Complex.ofReal_natCast, A] using hh
  -- Mellin inversion gives the defective theta relation for the actual integer measure.
  let ν := beurlingSystemIntegerMeasure B
  have hsupp : ν (Iio 1) = 0 := beurlingSystemIntegerMeasure_Iio_one_eq_zero B
  have hmom : Integrable (fun u : ℝ => u ^ (-(3 / 2 : ℝ))) ν :=
    integrable_rpow_beurlingSystemIntegerMeasure B hBsum
  have hmom2 := integrable_inv_sq_of_integrable_rpow_neg_three_halves hsupp hmom
  haveI : SigmaFinite ν := sigmaFinite_of_measure_Iio_one_eq_zero hsupp hmom2
  have hθm : MellinConvergent (measureTheta ν) (3 / 4) := by
    have hh := hasMellin_measureTheta hsupp (s := (3 / 2 : ℂ)) (by norm_num)
      (by simpa using hmom) hmom2
    simpa [show ((3 / 2 : ℂ) / 2) = (3 / 4 : ℂ) by ring] using hh.1
  have hR' : ∀ s : ℂ, s.re = 3 / 2 →
      mellin (measureTheta ν) (s / 2) = E s + β * Complex.Gammaℝ (s - 1) := by
    intro s hs
    have hm := hasMellin_measureTheta hsupp (s := s) (by linarith only [hs])
      (by rw [hs]; exact hmom) hmom2
    rw [hm.2, show ν = beurlingSystemIntegerMeasure B from rfl,
      measureDirichlet_beurlingSystemIntegerMeasure]
    exact hR s hs
  have him : ∀ t : ℝ, (2 * (((1 / 4 : ℝ) : ℂ) + t * I)).im / 2 = t := fun t => by simp
  have hdint : Integrable fun t : ℝ => Complex.Gammaℝ (2 * (((1 / 4 : ℝ) : ℂ) + t * I)) *
      g ((2 * (((1 / 4 : ℝ) : ℂ) + t * I)).im / 2) := by
    simp only [him]
    exact integrable_Gammaℝ_mul hgm.aestronglyMeasurable hgb
  have hθ : ∀ x : ℝ, 0 < x → freqTheta (fun n => ((A n : ℝ) : ℂ)) lam x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * freqTheta (fun n => ((A n : ℝ) : ℂ)) lam x⁻¹ +
        -β + β * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x := by
    intro x hx
    have hh := critical_line_even_theta_relation_defect
      (d := fun s => Complex.Gammaℝ s * g (s.im / 2))
      (continuousOn_measureTheta hsupp hmom2) hθm hEc hEd hdecay hR' hC hdint hx
    simp only [him, ν, measureTheta_beurlingSystemIntegerMeasure,
      htheta x hx, htheta x⁻¹ (inv_pos.mpr hx)] at hh
    unfold defectKernel
    linear_combination hh
  have hβreal := pole_coefficient_real_of_theta_defect ha0 hlam ha hgm hgb hgi hθ
  have hθreal : ∀ x : ℝ, 0 < x → freqTheta (fun n => ((A n : ℝ) : ℂ)) lam x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * freqTheta (fun n => ((A n : ℝ) : ℂ)) lam x⁻¹ +
        -(β.re : ℂ) + (β.re : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x := by
    simpa only [hβreal] using hθ
  have hC0 := tendsto_abelCos_zero_of_theta_defect ha0 hlam ha hgm hgb hgi hθreal
  have hβpos : 0 ≤ β.re := by
    have hh : 0 ≤ β.re / Real.pi := le_of_tendsto_of_tendsto
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[>] 0) (𝓝 0)) hC0 (by
        filter_upwards [self_mem_nhdsWithin] with ε hε
        simp only [abelCos, mul_zero, Real.cos_zero, mul_one]
        exact mul_nonneg hε.le (tsum_nonneg fun n => mul_nonneg (ha0 n) (Real.exp_pos _).le))
    have hmul := mul_nonneg hh Real.pi_pos.le
    rwa [div_mul_cancel₀ _ Real.pi_ne_zero] at hmul
  have hbound := pole_residue_le_of_small_critical_line_defect B hBsum hEc hEd hdecay hR hC
    hgm hgb hgi hsmall
  have hsq : (2 * β.re) ^ 2 < 2 := by
    have hh := mul_nonneg (sub_nonneg.mpr hbound)
      (show (0 : ℝ) ≤ 19 / 16 + 2 * β.re by linarith only [hβpos])
    nlinarith only [hh]
  obtain ⟨hβhalf, hvals⟩ := integer_spectrum_of_residue_sq_lt_two hmono hlam0 hA1 ha hsq
    hgm hgb hgi hθreal
  have hnormnat : ∀ x : B.Integer, B.intNorm x = (index x : ℝ) + 1 :=
    fun x => (hnorm x).symm.trans (hvals (index x)).1
  have hinj : Function.Injective index := by
    intro x y hxy
    letI := (hfinite (index x)).fintype
    have hc : Fintype.card {z : B.Integer // index z = index x} ≤ 1 := by
      rw [← Nat.card_eq_fintype_card]
      exact (hvals (index x)).2.le
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
  refine ⟨?_, beurlingSystem_rigidity_of_integer_measure_eq B hν⟩
  rw [← hβreal, hβhalf]
  norm_num

end GaloisForLFunctions.ArithmeticPositiveDuality
