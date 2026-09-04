import GaloisForLFunctions.HTGeometry.CompactFourierEntire
import GaloisForLFunctions.Hurwitz.ExpIndependence
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Data.Nat.Prime.Int

/-!
# Prime Burnol finite modular support

Literal prime powers, square-root Euler amplitudes, and arbitrary ordinate clocks define a
source-native half-line Burnol packet. Every injectively labelled finite packet is linearly
independent, so its complete prime-mixed Gram is invertible before any Xi divisor is supplied.
-/

open Complex Matrix Set MeasureTheory
open scoped BigOperators ComplexOrder

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- Literal primitive prime-power valuation. -/
def primeBurnolValuation (pe : Nat.Primes × ℕ) : ℕ :=
  (pe.1 : ℕ) ^ (pe.2 + 1)

/-- Literal logarithmic frequency carried by a primitive prime-power cell. -/
def primeBurnolLogFrequency (pe : Nat.Primes × ℕ) : ℝ :=
  Real.log (primeBurnolValuation pe : ℝ)

theorem primeBurnolValuation_pos (pe : Nat.Primes × ℕ) :
    0 < primeBurnolValuation pe := by
  exact pow_pos pe.1.property.pos _

theorem primeBurnolValuation_one_lt (pe : Nat.Primes × ℕ) :
    1 < primeBurnolValuation pe := by
  exact one_lt_pow₀ pe.1.property.one_lt (Nat.succ_ne_zero pe.2)

theorem primeBurnolLogFrequency_pos (pe : Nat.Primes × ℕ) :
    0 < primeBurnolLogFrequency pe := by
  rw [primeBurnolLogFrequency]
  exact Real.log_pos (by exact_mod_cast primeBurnolValuation_one_lt pe)

/-- Prime-power uniqueness makes literal logarithmic source frequencies injective. -/
theorem primeBurnolLogFrequency_injective :
    Function.Injective primeBurnolLogFrequency := by
  rintro ⟨p, e⟩ ⟨q, f⟩ hlog
  have hpVal : (0 : ℝ) < primeBurnolValuation (p, e) := by
    exact_mod_cast primeBurnolValuation_pos (p, e)
  have hqVal : (0 : ℝ) < primeBurnolValuation (q, f) := by
    exact_mod_cast primeBurnolValuation_pos (q, f)
  have hvalR :
      (primeBurnolValuation (p, e) : ℝ) =
        (primeBurnolValuation (q, f) : ℝ) := by
    have hexp := congrArg Real.exp hlog
    rw [primeBurnolLogFrequency, primeBurnolLogFrequency,
      Real.exp_log hpVal, Real.exp_log hqVal] at hexp
    exact hexp
  have hpow : (p : ℕ) ^ (e + 1) = (q : ℕ) ^ (f + 1) := by
    exact_mod_cast hvalR
  obtain ⟨hpq, hef⟩ := Nat.Prime.pow_inj p.property q.property hpow
  apply Prod.ext
  · exact Subtype.ext hpq
  · exact hef

/-- Unsquared literal Euler amplitude: its square is `log p / p^(e+1)`. -/
def primeBurnolAmplitude (pe : Nat.Primes × ℕ) : ℂ :=
  (Real.sqrt
    (Real.log (pe.1 : ℝ) / (primeBurnolValuation pe : ℝ)) : ℝ)

theorem primeBurnolAmplitude_ne_zero (pe : Nat.Primes × ℕ) :
    primeBurnolAmplitude pe ≠ 0 := by
  rw [primeBurnolAmplitude]
  norm_cast
  apply ne_of_gt
  apply Real.sqrt_pos.2
  apply div_pos
  · exact Real.log_pos (by exact_mod_cast pe.1.property.one_lt)
  · exact_mod_cast primeBurnolValuation_pos pe

/-- Entire exponent of a literal prime-power Burnol column with arbitrary ordinate clock. -/
def primeBurnolComplexExponent
    (pe : Nat.Primes × ℕ) (kappa : ℝ) : ℂ :=
  -((primeBurnolLogFrequency pe : ℂ) + I * (kappa : ℂ))

/-- Different primitive cells retain distinct complex exponents for arbitrary clocks. -/
theorem primeBurnolComplexExponent_injective
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (kappa : Fin N → ℝ)
    (hpe : Function.Injective pe) :
    Function.Injective (fun i => primeBurnolComplexExponent (pe i) (kappa i)) := by
  intro i j hij
  apply hpe
  apply primeBurnolLogFrequency_injective
  have hre := congrArg Complex.re hij
  simp [primeBurnolComplexExponent] at hre
  linarith

/-- Literal source-native Burnol column. -/
def primeBurnolWindowFeature
    (pe : Nat.Primes × ℕ) (kappa L : ℝ) : ℂ :=
  primeBurnolAmplitude pe * (L : ℂ) *
    Complex.exp (primeBurnolComplexExponent pe kappa * (L : ℂ))

theorem continuous_primeBurnolWindowFeature
    (pe : Nat.Primes × ℕ) (kappa : ℝ) :
    Continuous (primeBurnolWindowFeature pe kappa) := by
  unfold primeBurnolWindowFeature
  fun_prop

theorem integrableOn_norm_sq_primeBurnolWindowFeature
    (pe : Nat.Primes × ℕ) (kappa : ℝ) :
    IntegrableOn
      (fun u : ℝ => ‖primeBurnolWindowFeature pe kappa u‖ ^ 2)
      (Ioi 0) := by
  let A := primeBurnolAmplitude pe
  let lambda := primeBurnolLogFrequency pe
  have hlambda : 0 < lambda := primeBurnolLogFrequency_pos pe
  have hbase : IntegrableOn
      (fun u : ℝ => u ^ 2 * Real.exp (-(2 * lambda) * u)) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (s := (2 : ℝ)) (p := (1 : ℝ)) (b := 2 * lambda)
      (by norm_num) (by norm_num) (by positivity)
    simpa [Real.rpow_two, Real.rpow_one] using h
  have hscaled : IntegrableOn
      (fun u : ℝ => ‖A‖ ^ 2 *
        (u ^ 2 * Real.exp (-(2 * lambda) * u))) (Ioi 0) :=
    hbase.const_mul (‖A‖ ^ 2)
  refine hscaled.congr_fun ?_ measurableSet_Ioi
  intro u hu
  have hu0 : 0 < u := mem_Ioi.mp hu
  have hexp : Real.exp (-(lambda * u)) ^ 2 =
      Real.exp (-(2 * lambda) * u) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  symm
  change ‖primeBurnolWindowFeature pe kappa u‖ ^ 2 = _
  rw [primeBurnolWindowFeature, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hu0, Complex.norm_exp, mul_pow, mul_pow]
  simp [primeBurnolComplexExponent, Complex.mul_re, lambda]
  rw [hexp]
  dsimp [A, lambda]
  ring_nf

abbrev primeBurnolHalfLineL2 :=
  Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))

theorem memLp_primeBurnolWindowFeature
    (pe : Nat.Primes × ℕ) (kappa : ℝ) :
    MemLp (primeBurnolWindowFeature pe kappa) 2
      (volume.restrict (Ioi (0 : ℝ))) := by
  exact (memLp_two_iff_integrable_sq_norm
    (continuous_primeBurnolWindowFeature pe kappa).aestronglyMeasurable.restrict).2
      (integrableOn_norm_sq_primeBurnolWindowFeature pe kappa)

def primeBurnolWindowFeatureLp
    (pe : Nat.Primes × ℕ) (kappa : ℝ) : primeBurnolHalfLineL2 :=
  (memLp_primeBurnolWindowFeature pe kappa).toLp
    (primeBurnolWindowFeature pe kappa)

theorem primeBurnolWindowFeatureLp_coeFn
    (pe : Nat.Primes × ℕ) (kappa : ℝ) :
    ((primeBurnolWindowFeatureLp pe kappa : primeBurnolHalfLineL2) : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioi (0 : ℝ))]
        primeBurnolWindowFeature pe kappa := by
  exact (memLp_primeBurnolWindowFeature pe kappa).coeFn_toLp

theorem coeFn_finset_sum_smul_primeBurnolWindowFeatureLp
    {N : ℕ} (s : Finset (Fin N)) (c : Fin N → ℂ)
    (pe : Fin N → Nat.Primes × ℕ) (kappa : Fin N → ℝ) :
    (((∑ i ∈ s, c i • primeBurnolWindowFeatureLp (pe i) (kappa i) :
        primeBurnolHalfLineL2) : primeBurnolHalfLineL2) : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioi (0 : ℝ))]
        fun L => ∑ i ∈ s,
          c i * primeBurnolWindowFeature (pe i) (kappa i) L := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact (Lp.coeFn_zero ℂ 2 (volume.restrict (Ioi (0 : ℝ)))).trans
        (Filter.Eventually.of_forall fun _ => rfl)
  | @insert i s hi ih =>
      filter_upwards [Lp.coeFn_add
          (c i • primeBurnolWindowFeatureLp (pe i) (kappa i))
          (∑ j ∈ s, c j • primeBurnolWindowFeatureLp (pe j) (kappa j)),
        Lp.coeFn_smul (c i)
          (primeBurnolWindowFeatureLp (pe i) (kappa i)),
        primeBurnolWindowFeatureLp_coeFn (pe i) (kappa i), ih] with
          L hadd hsmul hfeature hsum
      rw [Finset.sum_insert hi, hadd, Pi.add_apply, hsmul, Pi.smul_apply,
        smul_eq_mul, hfeature, hsum, Finset.sum_insert hi]

/-- Every injectively labelled finite literal Burnol packet is linearly independent. -/
theorem primeBurnolWindowFeatureLp_linearIndependent
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (hpe : Function.Injective pe)
    (kappa : Fin N → ℝ) :
    LinearIndependent ℂ (fun i => primeBurnolWindowFeatureLp (pe i) (kappa i)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hzeroCoe :
      (((∑ j, c j • primeBurnolWindowFeatureLp (pe j) (kappa j) :
          primeBurnolHalfLineL2) : primeBurnolHalfLineL2) : ℝ → ℂ)
        =ᵐ[volume.restrict (Ioi (0 : ℝ))] fun _ => 0 := by
    rw [hc]
    exact Lp.coeFn_zero ℂ 2 (volume.restrict (Ioi (0 : ℝ)))
  have hrawAE :
      (fun L : ℝ => ∑ j,
        c j * primeBurnolWindowFeature (pe j) (kappa j) L)
        =ᵐ[volume.restrict (Ioi (0 : ℝ))] fun _ => 0 :=
    (coeFn_finset_sum_smul_primeBurnolWindowFeatureLp
      Finset.univ c pe kappa).symm.trans hzeroCoe
  let beta : Fin N → ℂ := fun j =>
    primeBurnolComplexExponent (pe j) (kappa j)
  let coeff : Fin N → ℂ := fun j => c j * primeBurnolAmplitude (pe j)
  let G : ℂ → ℂ := fun z => ∑ j, coeff j * z * Complex.exp (beta j * z)
  have hGdiff : Differentiable ℂ G := by
    dsimp [G]
    fun_prop
  have hGaeHalf :
      (fun L : ℝ => G (L : ℂ))
        =ᵐ[volume.restrict (Ioi (0 : ℝ))] fun _ => 0 := by
    filter_upwards [hrawAE] with L hL
    rw [show G (L : ℂ) =
        ∑ j, c j * primeBurnolWindowFeature (pe j) (kappa j) L by
      dsimp [G, coeff, beta]
      apply Finset.sum_congr rfl
      intro j _hj
      rw [primeBurnolWindowFeature]
      ring]
    exact hL
  have hsub : Ioo (2 : ℝ) 4 ⊆ Ioi (0 : ℝ) := by
    intro L hL
    exact lt_trans (by norm_num) hL.1
  have hGaeInterval :
      (fun L : ℝ => G (L : ℂ))
        =ᵐ[volume.restrict (Ioo (2 : ℝ) 4)] fun _ => 0 :=
    hGaeHalf.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
  have hGall : ∀ z : ℂ, G z = 0 := by
    intro z
    exact entire_eq_zero_of_ae_vanishing_on_real_interval
      (t₀ := (3 : ℝ)) (r := (1 : ℝ)) hGdiff (by norm_num)
      (by
        norm_num
        rw [Filter.eventually_inf_principal]
        apply (ae_restrict_iff' measurableSet_Ioo).mp
        simpa only [Filter.EventuallyEq] using hGaeInterval) z
  have hbeta : Function.Injective beta :=
    primeBurnolComplexExponent_injective pe kappa hpe
  have hcoeff : coeff = 0 := by
    apply HurwitzExp.expLin_eq_zero_on_open hbeta isOpen_compl_singleton
      (Set.nonempty_compl.mpr (Set.singleton_ne_univ 0))
    intro z hz
    have hz0 : z ≠ 0 := by simpa using hz
    have hfactor :
        G z = z * ∑ j, coeff j * Complex.exp (beta j * z) := by
      dsimp [G]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    have hprod : z * ∑ j, coeff j * Complex.exp (beta j * z) = 0 := by
      rw [← hfactor]
      exact hGall z
    exact (mul_eq_zero.mp hprod).resolve_left hz0
  have hci : coeff i = 0 := congrFun hcoeff i
  dsimp [coeff] at hci
  exact (mul_eq_zero.mp hci).resolve_right (primeBurnolAmplitude_ne_zero (pe i))

/-- Complete finite literal prime-mixed Burnol Gram. -/
def primeBurnolWindowGramMatrix {N : ℕ}
    (pe : Fin N → Nat.Primes × ℕ) (kappa : Fin N → ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.gram ℂ (fun i => primeBurnolWindowFeatureLp (pe i) (kappa i))

theorem det_primeBurnolWindowGramMatrix_ne_zero
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (hpe : Function.Injective pe)
    (kappa : Fin N → ℝ) :
    (primeBurnolWindowGramMatrix pe kappa).det ≠ 0 := by
  exact Matrix.det_gram_ne_zero_iff_linearIndependent.mpr
    (primeBurnolWindowFeatureLp_linearIndependent pe hpe kappa)

/-- Every finite literal Burnol Gram is a unit; its modular inverse is canonical. -/
theorem primeBurnolWindowGramMatrix_isUnit
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (hpe : Function.Injective pe)
    (kappa : Fin N → ℝ) :
    IsUnit (primeBurnolWindowGramMatrix pe kappa) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  exact isUnit_iff_ne_zero.mpr
    (det_primeBurnolWindowGramMatrix_ne_zero pe hpe kappa)

end

end RHTower
