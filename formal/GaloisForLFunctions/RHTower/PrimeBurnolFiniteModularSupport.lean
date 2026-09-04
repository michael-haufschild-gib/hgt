import GaloisForLFunctions.RHTower.RoutePPrimitiveBurnolMatrixCompleteColligation
import GaloisForLFunctions.RHTower.XiWardCubicScalarSourceBohrSquaringWall
import GaloisForLFunctions.HTGeometry.CompactFourierEntire
import GaloisForLFunctions.Hurwitz.ExpIndependence

/-!
# Prime Burnol finite modular support

Every injective finite packet of literal primitive Burnol window columns is linearly independent,
for arbitrary ordinate clocks.  Its complete source Gram is therefore invertible before any Xi
divisor is supplied.  This gives canonical finite modular densities for ULF-MCCED-001 without a
pseudoinverse or support choice.
-/

open Complex Matrix Set MeasureTheory
open scoped BigOperators ComplexOrder

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- Entire exponent of a literal primitive Burnol column. -/
def primeBurnolComplexExponent
    (pe : Nat.Primes × ℕ) (kappa : ℝ) : ℂ :=
  -(routePPrimitiveBurnolSpectralPoint pe kappa - 1 / 2)

/-- Injective primitive labels remain distinct after arbitrary ordinate clocks are added. -/
theorem primeBurnolComplexExponent_injective
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (kappa : Fin N → ℝ)
    (hpe : Function.Injective pe) :
    Function.Injective (fun i => primeBurnolComplexExponent (pe i) (kappa i)) := by
  intro i j hij
  apply hpe
  apply xiGammaEulerPrimitiveLogFrequency_injective
  have hre := congrArg Complex.re hij
  simp [primeBurnolComplexExponent,
    routePPrimitiveBurnolSpectralPoint_re] at hre
  linarith

/-- The source window is a nonzero Euler amplitude times one conormal-clock exponential. -/
theorem routePPrimitiveBurnolWindowFeature_eq_complexExponent
    (pe : Nat.Primes × ℕ) (kappa L : ℝ) :
    routePPrimitiveBurnolWindowFeature pe kappa L =
      finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat pe) *
        (L : ℂ) * Complex.exp (primeBurnolComplexExponent pe kappa * (L : ℂ)) := by
  rw [routePPrimitiveBurnolWindowFeature,
    xiWardCubicBurnolWindowConormalFeature_eq,
    routePXiBaseConormalResidueFeature]
  simp only [primeBurnolComplexExponent]
  rw [show -((routePPrimitiveBurnolSpectralPoint pe kappa - 1 / 2) * (L : ℂ)) =
      -(routePPrimitiveBurnolSpectralPoint pe kappa - 1 / 2) * (L : ℂ) by ring]
  ring

/-- The Hilbert column has the literal source window as its almost-everywhere representative. -/
theorem routePPrimitiveBurnolWindowFeatureLp_coeFn
    (pe : Nat.Primes × ℕ) (kappa : ℝ) :
    ((routePPrimitiveBurnolWindowFeatureLp pe kappa : routePBurnolHalfLineL2) :
        ℝ → ℂ) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      routePPrimitiveBurnolWindowFeature pe kappa := by
  rw [routePPrimitiveBurnolWindowFeatureLp, routePBurnolHalfLineL2Of]
  exact (memLp_routePBurnolHalfLine
    (continuous_routePPrimitiveBurnolWindowFeature pe kappa)
    (integrableOn_norm_sq_routePPrimitiveBurnolWindowFeature pe kappa)).coeFn_toLp

/-- Literal primitive Euler amplitudes never vanish. -/
theorem finiteVonMangoldtDepthOneAmplitude_primitive_source_ne_zero
    (pe : Nat.Primes × ℕ) :
    finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat pe) ≠ 0 := by
  rw [finiteVonMangoldtDepthOneAmplitude]
  norm_cast
  apply ne_of_gt
  apply Real.sqrt_pos.2
  apply div_pos
  · rw [xiGammaEulerValuationNat, vonMangoldt_prime_pow_succ_eq_log pe]
    exact Real.log_pos (by exact_mod_cast pe.1.property.one_lt)
  · exact_mod_cast pow_pos pe.1.property.pos (pe.2 + 1)

/-- Finite Hilbert combinations retain their literal source representatives. -/
theorem coeFn_finset_sum_smul_routePPrimitiveBurnolWindowFeatureLp
    {N : ℕ} (s : Finset (Fin N)) (c : Fin N → ℂ)
    (pe : Fin N → Nat.Primes × ℕ) (kappa : Fin N → ℝ) :
    (((∑ i ∈ s, c i • routePPrimitiveBurnolWindowFeatureLp (pe i) (kappa i) :
        routePBurnolHalfLineL2) : routePBurnolHalfLineL2) : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioi (0 : ℝ))]
        fun L => ∑ i ∈ s,
          c i * routePPrimitiveBurnolWindowFeature (pe i) (kappa i) L := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact (Lp.coeFn_zero ℂ 2 (volume.restrict (Ioi (0 : ℝ)))).trans
        (Filter.Eventually.of_forall fun _ => rfl)
  | @insert i s hi ih =>
      filter_upwards [Lp.coeFn_add
          (c i • routePPrimitiveBurnolWindowFeatureLp (pe i) (kappa i))
          (∑ j ∈ s, c j • routePPrimitiveBurnolWindowFeatureLp (pe j) (kappa j)),
        Lp.coeFn_smul (c i)
          (routePPrimitiveBurnolWindowFeatureLp (pe i) (kappa i)),
        routePPrimitiveBurnolWindowFeatureLp_coeFn (pe i) (kappa i), ih] with
          L hadd hsmul hfeature hsum
      rw [Finset.sum_insert hi, hadd, Pi.add_apply, hsmul, Pi.smul_apply,
        smul_eq_mul, hfeature, hsum, Finset.sum_insert hi]

/-- **Prime Burnol finite modular support.**  Every injectively labelled finite packet is linearly
independent in the actual half-line Hilbert source, for arbitrary ordinate clocks. -/
theorem routePPrimitiveBurnolWindowFeatureLp_linearIndependent
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (hpe : Function.Injective pe)
    (kappa : Fin N → ℝ) :
    LinearIndependent ℂ
      (fun i => routePPrimitiveBurnolWindowFeatureLp (pe i) (kappa i)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hzeroCoe :
      (((∑ j, c j • routePPrimitiveBurnolWindowFeatureLp (pe j) (kappa j) :
          routePBurnolHalfLineL2) : routePBurnolHalfLineL2) : ℝ → ℂ)
        =ᵐ[volume.restrict (Ioi (0 : ℝ))] fun _ => 0 := by
    rw [hc]
    exact Lp.coeFn_zero ℂ 2 (volume.restrict (Ioi (0 : ℝ)))
  have hrawAE :
      (fun L : ℝ => ∑ j,
        c j * routePPrimitiveBurnolWindowFeature (pe j) (kappa j) L)
        =ᵐ[volume.restrict (Ioi (0 : ℝ))] fun _ => 0 :=
    (coeFn_finset_sum_smul_routePPrimitiveBurnolWindowFeatureLp
      Finset.univ c pe kappa).symm.trans hzeroCoe
  let beta : Fin N → ℂ := fun j =>
    primeBurnolComplexExponent (pe j) (kappa j)
  let coeff : Fin N → ℂ := fun j =>
    c j * finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat (pe j))
  let G : ℂ → ℂ := fun z => ∑ j, coeff j * z * Complex.exp (beta j * z)
  have hGdiff : Differentiable ℂ G := by
    dsimp [G]
    fun_prop
  have hGaeHalf :
      (fun L : ℝ => G (L : ℂ))
        =ᵐ[volume.restrict (Ioi (0 : ℝ))] fun _ => 0 := by
    filter_upwards [hrawAE] with L hL
    rw [show G (L : ℂ) =
        ∑ j, c j * routePPrimitiveBurnolWindowFeature (pe j) (kappa j) L by
      dsimp [G, coeff, beta]
      apply Finset.sum_congr rfl
      intro j _hj
      rw [routePPrimitiveBurnolWindowFeature_eq_complexExponent]
      ring]
    exact hL
  have hsub : Ioo (2 : ℝ) 4 ⊆ Ioi (0 : ℝ) := by
    intro L hL
    exact lt_trans (by norm_num) hL.1
  have hGaeInterval :
      (fun L : ℝ => G (L : ℂ))
        =ᵐ[volume.restrict (Ioo (2 : ℝ) 4)] fun _ => 0 :=
    hGaeHalf.filter_mono
      (ae_mono (Measure.restrict_mono hsub le_rfl))
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
  exact (mul_eq_zero.mp hci).resolve_right
    (finiteVonMangoldtDepthOneAmplitude_primitive_source_ne_zero (pe i))

/-- The complete finite prime-mixed Burnol covariance has nonzero determinant. -/
theorem det_routePPrimitiveBurnolWindowGramMatrix_ne_zero
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (hpe : Function.Injective pe)
    (kappa : Fin N → ℝ) :
    (routePPrimitiveBurnolWindowGramMatrix pe kappa).det ≠ 0 := by
  rw [routePPrimitiveBurnolWindowGramMatrix_eq_gram_L2]
  exact Matrix.det_gram_ne_zero_iff_linearIndependent.mpr
    (routePPrimitiveBurnolWindowFeatureLp_linearIndependent pe hpe kappa)

/-- Every finite literal Burnol density is a unit, so its modular inverse is canonical. -/
theorem routePPrimitiveBurnolWindowGramMatrix_isUnit
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (hpe : Function.Injective pe)
    (kappa : Fin N → ℝ) :
    IsUnit (routePPrimitiveBurnolWindowGramMatrix pe kappa) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  exact isUnit_iff_ne_zero.mpr
    (det_routePPrimitiveBurnolWindowGramMatrix_ne_zero pe hpe kappa)

end

end RHTower
