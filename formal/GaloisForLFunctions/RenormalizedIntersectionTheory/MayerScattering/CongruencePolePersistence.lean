import GaloisForLFunctions.RHTower.SelbergEisensteinCuspExpansion
import GaloisForLFunctions.RHTower.SelbergKernelBetaIntegral
import GaloisForLFunctions.RHTower.VisibleCoprimeDirichletZeroJet
import GaloisForLFunctions.HTGeometry.RealBaseCpowPolar
import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerBoundaryResolvent

/-! Principal congruence Eisenstein constant terms at infinity have the same
scattering pole divisor at every level and height. The comparison starts from the
literal Poincaré Fourier expansion and retains zero multiplicities. -/

open Complex UpperHalfPlane
open scoped FourierTransform ArithmeticFunction.Moebius
open GaloisForLFunctions.RHTower
open GaloisForLFunctions.RenormalizedIntersectionTheory
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.CongruenceScattering

/-- Möbius inversion identifies the coprimality-restricted series with the
reciprocal principal Dirichlet L-function. -/
theorem moebius_series_eq (M : ℕ) [NeZero M] {w : ℂ} (hw : 1 < w.re) :
    LSeries (TotientMulLSeries.muChi M) w =
      (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) w)⁻¹ := by
  rw [DirichletCharacter.LFunction_eq_LSeries _ hw]
  have h := DirichletCharacter.LSeries.mul_mu_eq_one (1 : DirichletCharacter ℂ M) hw
  rw [← eq_inv_of_mul_eq_one_right h]
  apply LSeries_congr _ w
  intro n hn
  simp only [TotientMulLSeries.muChi, ArithmeticFunction.pmul_apply,
    TotientMulMoebius.chi, ArithmeticFunction.coe_mk, ne_eq, hn,
    not_false_eq_true, true_and, Int.cast_mul, Pi.mul_apply]
  by_cases hc : n.Coprime M
  · rw [if_pos hc, MulChar.one_apply ((ZMod.isUnit_iff_coprime n M).mpr hc)]
    simp
  · rw [if_neg hc, MulChar.map_nonunit _
      (fun h => hc ((ZMod.isUnit_iff_coprime n M).mp h))]
    simp

/-- The principal reciprocal has only the zeta denominator and finite local factors. -/
theorem moebius_series_eq_euler (M : ℕ) [NeZero M] {w : ℂ} (hw : 1 < w.re) :
    LSeries (TotientMulLSeries.muChi M) w =
      (riemannZeta w * _root_.RHTower.principalDirichletEulerProduct M w)⁻¹ := by
  rw [moebius_series_eq M hw]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne M)
  rw [_root_.RHTower.principalLFunction_eq_zeta_mul_eulerProduct m
    (by intro h; simp [h] at hw)]

private theorem beta_eq_arch (s : ℂ) :
    SelbergKernelBetaIntegral.cBeta s = MayerScatteringNormalization.archimedeanFactor s := by
  have hp : (Real.sqrt Real.pi : ℂ) = (Real.pi : ℂ) ^ (1 / 2 : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow Real.pi_pos.le]
    norm_num
  simp only [SelbergKernelBetaIntegral.cBeta,
    MayerScatteringNormalization.archimedeanFactor, hp, div_eq_mul_inv]

/-- The nonvanishing level and height multiplier of the level-one scattering entry. -/
def levelFactor (N : ℕ) (z : ℍ) (s : ℂ) : ℂ :=
  2 * cexp (-s * (Real.log ((N : ℝ) ^ 2) : ℂ)) *
    cexp (-s * (Real.log N : ℂ)) * ((z.im / N : ℝ) : ℂ) ^ (1 - s) *
    ((N ^ 2).totient : ℂ) / (N.totient : ℂ) /
      _root_.RHTower.principalDirichletEulerProduct (N ^ 2) (2 * s)

/-- The source normalization simplifies to the level Euler correction
`2 N^(-2s) y^(1-s) / ∏_{p∣N}(1-p^(-2s))`. -/
theorem levelFactor_eq (N : ℕ) [NeZero N] (z : ℍ) (s : ℂ) :
    levelFactor N z s =
      2 * cexp (-(2 * s) * (Real.log N : ℂ)) * (z.im : ℂ) ^ (1 - s) /
        _root_.RHTower.principalDirichletEulerProduct N (2 * s) := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hφpos : 0 < N.totient := Nat.totient_pos.mpr hN
  have hφ₀ : (N.totient : ℂ) ≠ 0 := by exact_mod_cast hφpos.ne'
  have hφ : (N ^ 2).totient = N * N.totient := by
    apply Nat.eq_of_mul_eq_mul_left hφpos
    have h := Nat.totient_gcd_mul_totient_mul N N
    rw [Nat.gcd_self] at h
    calc N.totient * (N ^ 2).totient = N.totient * N.totient * N := by
           simpa only [pow_two] using h
         _ = N.totient * (N * N.totient) := by ring
  have hφC : ((N ^ 2).totient : ℂ) = (N : ℂ) * (N.totient : ℂ) := by
    exact_mod_cast hφ
  have hNexp : (N : ℂ) = cexp (Real.log (N : ℝ)) := by
    rw [← Complex.ofReal_exp, Real.exp_log hNR]
    simp
  have hscale : cexp (-s * (Real.log ((N : ℝ) ^ 2) : ℂ)) *
      cexp (-s * (Real.log N : ℂ)) * ((z.im / N : ℝ) : ℂ) ^ (1 - s) * (N : ℂ) =
      cexp (-(2 * s) * (Real.log N : ℂ)) * (z.im : ℂ) ^ (1 - s) := by
    rw [HTGeometry.ofReal_cpow_eq_exp (div_pos z.im_pos hNR),
      HTGeometry.ofReal_cpow_eq_exp z.im_pos, hNexp, Real.log_pow,
      Real.log_div z.im_pos.ne' hNR.ne']
    push_cast
    simp only [← Complex.exp_add]
    congr 1
    ring
  have hEuler : _root_.RHTower.principalDirichletEulerProduct (N ^ 2) (2 * s) =
      _root_.RHTower.principalDirichletEulerProduct N (2 * s) := by
    simp only [_root_.RHTower.principalDirichletEulerProduct,
      Nat.primeFactors_pow N (by norm_num : (2 : ℕ) ≠ 0)]
  rw [levelFactor, hφC, hEuler]
  have hnum : 2 * cexp (-s * (Real.log ((N : ℝ) ^ 2) : ℂ)) *
      cexp (-s * (Real.log N : ℂ)) * ((z.im / N : ℝ) : ℂ) ^ (1 - s) *
      ((N : ℂ) * (N.totient : ℂ)) / (N.totient : ℂ) =
      2 * (cexp (-s * (Real.log ((N : ℝ) ^ 2) : ℂ)) *
        cexp (-s * (Real.log N : ℂ)) * ((z.im / N : ℝ) : ℂ) ^ (1 - s) * (N : ℂ)) := by
    field_simp
  rw [hnum, hscale]
  ring

/-- Meromorphic continuation of the reflected constant term in the literal
principal congruence Poincaré Fourier expansion. -/
def continuedConstantTerm (N : ℕ) (z : ℍ) (s : ℂ) : ℂ :=
  levelFactor N z s * MayerScatteringNormalization.scatteringEntry s

/-- The continuation agrees with the source constant term throughout its
original convergent half-plane. -/
theorem constantTerm_eq (N : ℕ) [NeZero N] (z : ℍ) {s : ℂ} (hs : 1 / 2 < s.re) :
    SelbergEisensteinContinuation.constTerm N s z = continuedConstantTerm N z s := by
  have hw : 1 < (2 * s).re := by norm_num [Complex.mul_re]; linarith only [hs]
  rw [SelbergEisensteinContinuation.constTerm, moebius_series_eq_euler (N ^ 2) hw,
    SelbergEisensteinContinuation.pref, SelbergEisensteinCuspExpansion.fourier_ker0_zero,
    SelbergKernelBetaIntegral.integral_ker01 hs, beta_eq_arch]
  simp only [continuedConstantTerm, levelFactor, MayerScatteringNormalization.scatteringEntry,
    mul_inv_rev, div_eq_mul_inv]
  ring

/-- The literal Poincaré series has the continued constant term in its
Fourier expansion on the absolute-convergence chamber. -/
theorem poincare_eq (N : ℕ) [NeZero N] (hN : 3 ≤ N) (z : ℍ) {s : ℂ} (hs : 1 < s.re) :
    SelbergPoincare.poincare N 0 s z = (z.im : ℂ) ^ s +
      continuedConstantTerm N z s + SelbergEisensteinStar.Estar N s z := by
  rw [SelbergEisensteinContinuation.eisenstein_eq N hN hs z,
    constantTerm_eq N z (by linarith)]

private theorem height_pos (N : ℕ) [NeZero N] (z : ℍ) : 0 < z.im / N :=
  div_pos z.im_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N))

/-- All level and height corrections are analytic units in the source half-plane. -/
theorem levelFactor_analytic_unit (N : ℕ) [NeZero N] (z : ℍ) {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ (levelFactor N z) s ∧ levelFactor N z s ≠ 0 := by
  have hφ : (N.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))).ne'
  have hφ₂ : ((N ^ 2).totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (pow_pos (Nat.pos_of_ne_zero (NeZero.ne N)) 2)).ne'
  have hE := _root_.RHTower.principalDirichletEulerProduct_ne_zero_of_re_pos
    (N := N ^ 2) (s := 2 * s) (by simpa using mul_pos (by norm_num : (0 : ℝ) < 2) hs)
  have hEa : AnalyticAt ℂ
      (fun v : ℂ => _root_.RHTower.principalDirichletEulerProduct (N ^ 2) (2 * v)) s :=
    (_root_.RHTower.principalDirichletEulerProduct_analyticAt (N ^ 2) (2 * s)).comp
      (f := fun v : ℂ => 2 * v) (analyticAt_const.mul analyticAt_id)
  have hpow : AnalyticAt ℂ (fun v : ℂ => ((z.im / N : ℝ) : ℂ) ^ (1 - v)) s :=
    analyticAt_const.cpow (analyticAt_const.sub analyticAt_id)
      (Complex.ofReal_mem_slitPlane.mpr (height_pos N z))
  constructor
  · exact (((((analyticAt_const.mul ((analyticAt_id.neg.mul analyticAt_const).cexp)).mul
      ((analyticAt_id.neg.mul analyticAt_const).cexp)).mul hpow).mul analyticAt_const).div
      analyticAt_const hφ).div hEa hE
  · exact div_ne_zero (div_ne_zero (mul_ne_zero (mul_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) (Complex.exp_ne_zero _))
        (Complex.exp_ne_zero _)) (Complex.cpow_ne_zero_iff.mpr
          (Or.inl (Complex.ofReal_ne_zero.mpr (height_pos N z).ne')))) hφ₂) hφ) hE

/-- The actual constant term continues meromorphically across the line
`Re s = 1/2` to the right half-plane. -/
theorem meromorphicOn_constantTerm (N : ℕ) [NeZero N] (z : ℍ) :
    MeromorphicOn (continuedConstantTerm N z) {s : ℂ | 0 < s.re} := by
  intro s hs
  exact (levelFactor_analytic_unit N z hs).1.meromorphicAt.mul
    (MayerScatteringNormalization.meromorphic_scatteringEntry s)

/-- Congruence level and height preserve every scattering pole and its multiplicity. -/
theorem constantTerm_order (N : ℕ) [NeZero N] (z : ℍ) {w : ℂ}
    (h0 : 0 < w.re) (h1 : w.re < 1) :
    meromorphicOrderAt (continuedConstantTerm N z) (w / 2) =
      -((analyticOrderNatAt riemannZeta w : ℤ) : WithTop ℤ) := by
  obtain ⟨hU, hU₀⟩ := levelFactor_analytic_unit N z (s := w / 2)
    (by simpa using div_pos h0 (by norm_num : (0 : ℝ) < 2))
  change meromorphicOrderAt (levelFactor N z * MayerScatteringNormalization.scatteringEntry) _ = _
  rw [meromorphicOrderAt_mul_of_ne_zero hU hU₀, MayerBoundaryResolvent.scattering_order h0 h1]

/-- A pole of the continued congruence constant term is exactly a zeta zero. -/
theorem constantTerm_pole_iff (N : ℕ) [NeZero N] (z : ℍ) {w : ℂ}
    (h0 : 0 < w.re) (h1 : w.re < 1) :
    meromorphicOrderAt (continuedConstantTerm N z) (w / 2) < 0 ↔ riemannZeta w = 0 := by
  rw [constantTerm_order N z h0 h1, ← MayerBoundaryResolvent.scattering_order h0 h1]
  exact MayerBoundaryResolvent.scattering_pole_iff h0 h1

/-- Both constant Fourier modes, including the incoming power. -/
def fullConstantTerm (N : ℕ) (z : ℍ) (s : ℂ) : ℂ :=
  (z.im : ℂ) ^ s + continuedConstantTerm N z s

private theorem incoming_analytic (z : ℍ) (s : ℂ) :
    AnalyticAt ℂ (fun v : ℂ => (z.im : ℂ) ^ v) s :=
  analyticAt_const.cpow analyticAt_id (Complex.ofReal_mem_slitPlane.mpr z.im_pos)

/-- The full constant Fourier coefficient continues meromorphically to
`Re s > 0`. -/
theorem meromorphicOn_fullConstantTerm (N : ℕ) [NeZero N] (z : ℍ) :
    MeromorphicOn (fullConstantTerm N z) {s : ℂ | 0 < s.re} := by
  intro s hs
  exact (incoming_analytic z s).meromorphicAt.add (meromorphicOn_constantTerm N z s hs)

private theorem incoming_order (z : ℍ) (s : ℂ) :
    meromorphicOrderAt (fun v : ℂ => (z.im : ℂ) ^ v) s = 0 := by
  have hne : (z.im : ℂ) ^ s ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr z.im_pos.ne'))
  rw [(incoming_analytic z s).meromorphicOrderAt_eq,
    (incoming_analytic z s).analyticOrderAt_eq_zero.mpr hne]
  rfl

/-- The incoming Fourier mode cannot cancel any reflected scattering pole. -/
theorem fullConstantTerm_order_of_zero (N : ℕ) [NeZero N] (z : ℍ) {w : ℂ}
    (h0 : 0 < w.re) (h1 : w.re < 1) (hw : riemannZeta w = 0) :
    meromorphicOrderAt (fullConstantTerm N z) (w / 2) =
      -((analyticOrderNatAt riemannZeta w : ℤ) : WithTop ℤ) := by
  have hp := (constantTerm_pole_iff N z h0 h1).mpr hw
  change meromorphicOrderAt ((fun v : ℂ => (z.im : ℂ) ^ v) +
    continuedConstantTerm N z) (w / 2) = _
  rw [meromorphicOrderAt_add_eq_right_of_lt (incoming_analytic z (w / 2)).meromorphicAt
    (by rwa [incoming_order]), constantTerm_order N z h0 h1]

/-- Even after adding the incoming mode, the full constant coefficient has
precisely the zeta poles, at every congruence level and height. -/
theorem fullConstantTerm_pole_iff (N : ℕ) [NeZero N] (z : ℍ) {w : ℂ}
    (h0 : 0 < w.re) (h1 : w.re < 1) :
    meromorphicOrderAt (fullConstantTerm N z) (w / 2) < 0 ↔ riemannZeta w = 0 := by
  constructor
  · intro hp
    by_contra hw
    have hC : 0 ≤ meromorphicOrderAt (continuedConstantTerm N z) (w / 2) :=
      le_of_not_gt (fun h => hw ((constantTerm_pole_iff N z h0 h1).mp h))
    have hsum := meromorphicOrderAt_add (incoming_analytic z (w / 2)).meromorphicAt
      (meromorphicOn_constantTerm N z (w / 2)
        (by simpa using div_pos h0 (by norm_num : (0 : ℝ) < 2)))
    rw [incoming_order, min_eq_left hC] at hsum
    exact (not_lt_of_ge hsum) hp
  · intro hw
    rw [fullConstantTerm_order_of_zero N z h0 h1 hw, ← constantTerm_order N z h0 h1]
    exact (constantTerm_pole_iff N z h0 h1).mpr hw

#print axioms moebius_series_eq_euler
#print axioms levelFactor_eq
#print axioms constantTerm_eq
#print axioms poincare_eq
#print axioms meromorphicOn_constantTerm
#print axioms constantTerm_order
#print axioms constantTerm_pole_iff
#print axioms meromorphicOn_fullConstantTerm
#print axioms fullConstantTerm_order_of_zero
#print axioms fullConstantTerm_pole_iff

end GaloisForLFunctions.RenormalizedIntersectionTheory.CongruenceScattering
