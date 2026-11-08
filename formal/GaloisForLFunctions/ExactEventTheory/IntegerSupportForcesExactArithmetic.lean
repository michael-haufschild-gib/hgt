import GaloisForLFunctions.ArithmeticPositiveDuality.IntegrableDefectsAtUnitDensityAreRigid
import GaloisForLFunctions.ArithmeticPositiveDuality.BeurlingNormsHaveAnOrderedIntegralSpectrum

/-!
# Integer support forces exact arithmetic

For integer frequencies the Abel cosine means at zero and one agree exactly. An integrable
uncompleted functional-equation defect preserves their radial residues. The unit atom therefore
fixes the pole residue, without a bound on the defect's size. Unit-density rigidity then recovers
the entire integer spectrum and, for an Euler product, its rational-prime generators.
-/

open Complex MeasureTheory Filter Topology Set
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.FreqHamburger
open GaloisForLFunctions.ArithmeticPositiveDuality RHTower.HamburgerStability

noncomputable section
namespace GaloisForLFunctions.ExactEventTheory

/-- The unit period of integer support identifies the Abel density with the first atom. -/
theorem integer_support_pins_pole_residue {a lam : ℕ → ℝ}
    (hmono : StrictMono lam) (hlam0 : lam 0 = 1)
    (hint : ∀ n, ∃ k : ℕ, lam n = k) (ha0 : ∀ n, 0 ≤ a n)
    (ha : Summable fun n => a n / lam n ^ 2) {β : ℝ}
    {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) (hgi : Integrable g)
    (hθ : ∀ x : ℝ, 0 < x → freqTheta (fun n => (a n : ℂ)) lam x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * freqTheta (fun n => (a n : ℂ)) lam x⁻¹ +
        -(β : ℂ) + (β : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x) :
    2 * β = a 0 := by
  have hlam : ∀ n, 1 ≤ lam n := fun n => hlam0 ▸ hmono.monotone (Nat.zero_le n)
  have hpos : ∀ n, 0 < lam n := fun n => zero_lt_one.trans_le (hlam n)
  have haC : Summable fun n => ‖(a n : ℂ)‖ / lam n ^ 2 :=
    ha.congr fun n => by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha0 n)]
  have hL := fun z hz => freqSeries_eq_of_theta_defect ha0 hlam ha hgm hgb hθ (z := z) hz
  obtain ⟨c, hc, hsep⟩ := exists_sep_of_strictMono hmono hpos 0
  have hres := tendsto_mul_freqSeries_atom (a := fun n => (a n : ℂ)) hlam haC rfl
    (hpos 0) hc hsep
  have hC1 := abel_limit_of_defective_series ha0 hlam ha hgm hgb hgi hL (hpos 0) hres
  have hC0 := tendsto_abelCos_zero_of_theta_defect ha0 hlam ha hgm hgb hgi hθ
  have hperiod : abelCos a lam (lam 0) = abelCos a lam 0 := by
    funext ε
    unfold abelCos
    congr 1
    apply tsum_congr
    intro n
    obtain ⟨k, hk⟩ := hint n
    have hcos : Real.cos (2 * Real.pi * lam n * lam 0) = 1 := by
      rw [hlam0, mul_one, hk, show 2 * Real.pi * (k : ℝ) = (k : ℝ) * (2 * Real.pi) by ring]
      exact Real.cos_nat_mul_two_pi k
    rw [hcos, mul_zero, Real.cos_zero]
  rw [hperiod] at hC1
  have he := tendsto_nhds_unique hC0 hC1
  have hre : ((a 0 : ℂ) / (2 * Real.pi)).re = a 0 / (2 * Real.pi) := by
    rw [show ((a 0 : ℂ) / (2 * Real.pi)) = ((a 0 / (2 * Real.pi) : ℝ) : ℂ) by
      push_cast; ring, Complex.ofReal_re]
  rw [hre, div_eq_div_iff Real.pi_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero)] at he
  nlinarith only [he, Real.pi_pos]

/-- Integer support and a unit first atom replace both a small-defect bound and a residue bound. -/
theorem integer_spectrum_of_integer_support_integrable_defect {a lam : ℕ → ℝ}
    (hmono : StrictMono lam) (hlam0 : lam 0 = 1)
    (hint : ∀ n, ∃ k : ℕ, lam n = k) (ha1 : ∀ n, 1 ≤ a n) (haunit : a 0 = 1)
    (ha : Summable fun n => a n / lam n ^ 2) {β : ℝ}
    {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) (hgi : Integrable g)
    (hθ : ∀ x : ℝ, 0 < x → freqTheta (fun n => (a n : ℂ)) lam x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * freqTheta (fun n => (a n : ℂ)) lam x⁻¹ +
        -(β : ℂ) + (β : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x) :
    β = 1 / 2 ∧ ∀ n, lam n = n + 1 ∧ a n = 1 := by
  have hβ := integer_support_pins_pole_residue hmono hlam0 hint
    (fun n => zero_le_one.trans (ha1 n)) ha hgm hgb hgi hθ
  rw [haunit] at hβ
  exact integer_spectrum_of_integrable_theta_defect hmono hlam0 ha1 ha
    (by linarith only [hβ]) hgm hgb hgi hθ

/-- An integer-norm Euler product with an integrable uncompleted Riemann FE defect is exactly ζ.
The defect may have arbitrary finite norm; all Hamburger strip assumptions are explicit. -/
theorem beurlingSystem_rigidity_of_integer_support_integrable_defect
    (B : RHTower.BeurlingSystem) [Countable B.Label] [Nonempty B.Label]
    (hint : ∀ x : B.Integer, ∃ k : ℕ, B.intNorm x = k)
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
  classical
  obtain ⟨lam, index, hmono, hlam0, hsurj, hnorm, hfinite⟩ := exists_ordered_beurling_norms B hBsum
  -- Finite norm fibers give positive integer atomic masses.
  let A : ℕ → ℕ := fun n => Nat.card {x : B.Integer // index x = n}
  have hA1 : ∀ n, 1 ≤ A n := by
    intro n
    letI : Fintype {x : B.Integer // index x = n} := (hfinite n).fintype
    obtain ⟨x, hx⟩ := hsurj n
    letI : Nonempty {x : B.Integer // index x = n} := ⟨⟨x, hx⟩⟩
    have hh : 0 < Fintype.card {x : B.Integer // index x = n} := Fintype.card_pos_iff.mpr inferInstance
    simp only [A, Nat.card_eq_fintype_card]
    omega
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
  obtain ⟨hβhalf, hvals⟩ := integer_spectrum_of_integer_support_integrable_defect
    hmono hlam0 hlamInt (fun n => by exact_mod_cast hA1 n)
    (by exact_mod_cast hunit0) ha hgm hgb hgi hθreal
  have hnormnat : ∀ x : B.Integer, B.intNorm x = (index x : ℝ) + 1 :=
    fun x => (hnorm x).symm.trans (hvals (index x)).1
  -- Unit multiplicities turn the norm index into a bijection with ℕ.
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
  refine ⟨?_, beurlingSystem_rigidity_of_integer_measure_eq B hν⟩
  rw [← hβreal, hβhalf]
  norm_num


end GaloisForLFunctions.ExactEventTheory
