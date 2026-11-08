import GaloisForLFunctions.ArithmeticPositiveDuality.IntegrableDefectsAtUnitDensityAreRigid
import GaloisForLFunctions.ArithmeticPositiveDuality.BeurlingNormsHaveAnOrderedIntegralSpectrum
import GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.NormCollisionAmplification

/-!
# Integrable functional-equation defects force unique norm factorization

The Abel residue of every atom is bounded by the total Abel density. Thus an integrable
uncompleted Riemann functional-equation defect bounds all norm multiplicities uniformly.
A multiplicative collision amplifies to arbitrarily large multiplicities, so none can occur.
The generator norms may be arbitrary real numbers; neither a residue bound nor a smallness
condition on the defect is imposed.
-/

open Complex MeasureTheory Filter Topology Set
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.FreqHamburger
open GaloisForLFunctions.ArithmeticPositiveDuality RHTower.HamburgerStability
open GaloisForLFunctions.SumProductArithmeticOfTheLogarithm

noncomputable section
namespace GaloisForLFunctions.ExactEventTheory

/-- An integrable defect bounds every atom's mass by the pole residue. -/
theorem atom_mass_le_of_integrable_theta_defect {a lam : ℕ → ℝ}
    (hmono : StrictMono lam) (hlam0 : lam 0 = 1) (ha0 : ∀ n, 0 ≤ a n)
    (ha : Summable fun n => a n / lam n ^ 2) {β : ℂ}
    {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) (hgi : Integrable g)
    (hθ : ∀ x : ℝ, 0 < x → freqTheta (fun n => (a n : ℂ)) lam x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * freqTheta (fun n => (a n : ℂ)) lam x⁻¹ +
        -β + β * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x) :
    ∀ m, a m ≤ 2 * β.re := by
  have hlam : ∀ n, 1 ≤ lam n := fun n => hlam0 ▸ hmono.monotone (Nat.zero_le n)
  have hpos : ∀ n, 0 < lam n := fun n => zero_lt_one.trans_le (hlam n)
  have haC : Summable fun n => ‖(a n : ℂ)‖ / lam n ^ 2 :=
    ha.congr fun n => by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha0 n)]
  have hβ := pole_coefficient_real_of_theta_defect ha0 hlam ha hgm hgb hgi hθ
  have hθreal : ∀ x : ℝ, 0 < x → freqTheta (fun n => (a n : ℂ)) lam x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * freqTheta (fun n => (a n : ℂ)) lam x⁻¹ +
        -(β.re : ℂ) + (β.re : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x := by
    simpa only [hβ] using hθ
  have hC0 := tendsto_abelCos_zero_of_theta_defect ha0 hlam ha hgm hgb hgi hθreal
  have hL := fun z hz => freqSeries_eq_of_theta_defect ha0 hlam ha hgm hgb hθ (z := z) hz
  intro m
  obtain ⟨c, hc, hsep⟩ := exists_sep_of_strictMono hmono hpos m
  have hres := tendsto_mul_freqSeries_atom (a := fun n => (a n : ℂ)) hlam haC rfl
    (hpos m) hc hsep
  have hCm := abel_limit_of_defective_series ha0 hlam ha hgm hgb hgi hL (hpos m) hres
  have hre : ((a m : ℂ) / (2 * Real.pi)).re = a m / (2 * Real.pi) := by
    rw [show ((a m : ℂ) / (2 * Real.pi)) = ((a m / (2 * Real.pi) : ℝ) : ℂ) by
      push_cast; ring, Complex.ofReal_re]
  rw [hre] at hCm
  have hh : a m / (2 * Real.pi) ≤ β.re / Real.pi := by
    apply le_of_tendsto_of_tendsto hCm hC0
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact abelCos_le_of_le hlam ha0 ha hε fun n => by simpa using Real.cos_le_one _
  have hp := Real.pi_pos
  rw [div_le_div_iff₀ (by positivity) hp] at hh
  nlinarith only [hh, hp]

/-- Integrable theta defects permit no equality between norms of distinct factorizations. -/
theorem intNorm_injective_of_integrable_theta_defect
    (B : RHTower.BeurlingSystem) [Countable B.Label] [Nonempty B.Label]
    (hBsum : Summable fun x : B.Integer => B.intNorm x ^ (-(3 / 2 : ℝ)))
    {β : ℂ} {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ}
    (hgm : Measurable g) (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) (hgi : Integrable g)
    (hθ : ∀ x : ℝ, 0 < x → beurlingTheta B x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * beurlingTheta B x⁻¹ +
        -β + β * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x) :
    Function.Injective B.intNorm := by
  classical
  obtain ⟨lam, index, hmono, hlam0, _, hnorm, hfinite⟩ := exists_ordered_beurling_norms B hBsum
  let A : ℕ → ℕ := fun n => Nat.card {x : B.Integer // index x = n}
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
  have hθ' : ∀ x : ℝ, 0 < x → freqTheta (fun n => ((A n : ℝ) : ℂ)) lam x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * freqTheta (fun n => ((A n : ℝ) : ℂ)) lam x⁻¹ +
        -β + β * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x := by
    intro x hx
    simpa only [htheta x hx, htheta x⁻¹ (inv_pos.mpr hx)] using hθ x hx
  have hmass := atom_mass_le_of_integrable_theta_defect hmono hlam0
    (fun n => Nat.cast_nonneg (A n)) ha hgm hgb hgi hθ'
  -- Every finite norm fiber is bounded by the same residue; multiplication rules out collisions.
  obtain ⟨K, hK⟩ := exists_nat_gt (2 * β.re)
  apply (uniform_finite_fibres_iff_norm_injective B).mp
  refine ⟨K, fun r S hS => ?_⟩
  by_cases hne : S.Nonempty
  · obtain ⟨u, hu⟩ := hne
    letI : Fintype {v : B.Integer // index v = index u} := (hfinite (index u)).fintype
    let f : {v : B.Integer // v ∈ S} → {v : B.Integer // index v = index u} :=
      fun v => ⟨v.val, hmono.injective (by rw [hnorm v.val, hnorm u, hS v.val v.property, hS u hu])⟩
    have hf : Function.Injective f := by
      intro v w h
      apply Subtype.ext
      exact congrArg (fun z : {v : B.Integer // index v = index u} => z.val) h
    have hc : S.card ≤ A (index u) := by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_coe, A] using
        Nat.card_le_card_of_injective f hf
    have hb : (A (index u) : ℝ) ≤ K := (hmass (index u)).trans hK.le
    exact hc.trans (by exact_mod_cast hb)
  · have hzero : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp only [hzero, Finset.card_empty, Nat.zero_le]

/-- In the Hamburger strip class, finite uncompleted FE defect forces unique factorization of
every real generalized-integer norm, without any lattice or small-defect assumption. -/
theorem intNorm_injective_of_integrable_critical_line_defect
    (B : RHTower.BeurlingSystem) [Countable B.Label] [Nonempty B.Label]
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
    Function.Injective B.intNorm := by
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
  apply intNorm_injective_of_integrable_theta_defect B hBsum hgm hgb hgi
  intro x hx
  have hh := critical_line_even_theta_relation_defect
    (d := fun s => Complex.Gammaℝ s * g (s.im / 2))
    (continuousOn_measureTheta hsupp hmom2) hθm hEc hEd hdecay hR' hC hdint hx
  simp only [him, ν, measureTheta_beurlingSystemIntegerMeasure] at hh
  unfold defectKernel
  linear_combination hh

end GaloisForLFunctions.ExactEventTheory

#print axioms GaloisForLFunctions.ExactEventTheory.intNorm_injective_of_integrable_theta_defect
#print axioms GaloisForLFunctions.ExactEventTheory.intNorm_injective_of_integrable_critical_line_defect
