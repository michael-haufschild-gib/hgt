import GaloisForLFunctions.ArithmeticHarmonicAnalysis.IntegerDilationThetaGammaIndependence
import GaloisForLFunctions.HTGeometry.AlgebraicIndependenceHasse

/-!
# Rational zeta dilations over the theta–Gamma field

All positive rational dilates `ζ(rs)` are jointly differentially independent over
`ℂ(s)⟨Γ, θ₂, θ₃, θ₄, E₂⟩`. Each finite jet packet admits a common denominator
`D`; its physical line `Re s=2D` transports exactly to the integer-dilation line.
Gamma coefficient separation then applies in the original physical variable.

Every positive rational Mahler orbit is independent precisely when its multiplier
is not one. This includes contracting orbits, although no single half-plane of
absolute convergence contains the entire rational dilation family.
-/

open Complex Filter Set Topology
open GaloisForLFunctions GaloisForLFunctions.HTGeometry RHTower
open scoped Differential UpperEndDifferentialInstances UpperEndComplexTowerInstances
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.GammaRational

local instance : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
local instance : Differential (RatFunc ℂ) := ratFuncCoordinateDifferential
local instance : DifferentialAlgebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncDifferentialAlgebra

/-- Positive rational dilation parameters. -/
abbrev Dilation := {r : ℚ // 0 < r}

/-- The actual rational dilation in the physical Dirichlet variable. -/
def zetaDilation (r : Dilation) (s : ℂ) : ℂ := riemannZeta ((r.1 : ℂ)*s)

private theorem dilation_re_pos (r : Dilation) : (0 : ℝ) < r.1 := by
  exact_mod_cast r.property

/-- Every positive rational dilation is analytic in the upper half-plane. -/
theorem zetaDilation_analytic_upper (r : Dilation) :
    AnalyticOnNhd ℂ (zetaDilation r) (upperTail 0) := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_upperTail 0)
  intro z hz
  have hc : (r.1 : ℂ) = ((r.1 : ℝ) : ℂ) := by norm_cast
  have hi : 0 < ((r.1 : ℂ)*z).im := by
    rw [hc]
    simpa only [mul_im, ofReal_re, ofReal_im, zero_mul, add_zero] using
      mul_pos (dilation_re_pos r) hz
  have hne : (r.1 : ℂ)*z ≠ 1 := by
    intro he
    rw [he] at hi
    norm_num at hi
  exact ((differentiableAt_riemannZeta hne).comp z
    (differentiableAt_id.const_mul _)).differentiableWithinAt

/-- Analytic germ of the literal rational dilation. -/
def zetaDilationAnalytic (r : Dilation) : upperEndAnalyticSubring :=
  ⟨Germ.coeRingHom upperEndFilter (zetaDilation r),
    ⟨zetaDilation r, 0, zetaDilation_analytic_upper r, rfl⟩⟩

/-- Actual rational dilations in the common meromorphic field. -/
def zetaDilationMero (r : Dilation) : upperEndMeroField :=
  algebraMap upperEndAnalyticSubring upperEndMeroField (zetaDilationAnalytic r)

/-- Each finite family can be moved to positive integer scales without moving its coefficients. -/
theorem exists_positive_integer_scales {J : Type*} [Fintype J] (r : J → Dilation) :
    ∃ D : ℕ, 0 < D ∧ ∃ m : J → ℕ, (∀ j, 0 < m j) ∧
      ∀ j, (D : ℚ)*(r j).1 = m j := by
  classical
  have hden : ∃ D : ℕ, 0 < D ∧ ∀ j, ∃ z : ℤ, (D : ℚ)*(r j).1 = z := by
    refine ⟨∏ j, (r j).1.den, Finset.prod_pos (fun j _ => Rat.den_pos _), fun j => ?_⟩
    obtain ⟨a, ha⟩ : (r j).1.den ∣ ∏ i, (r i).1.den :=
      Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
    refine ⟨(r j).1.num * a, ?_⟩
    rw [ha]
    push_cast
    linear_combination (a : ℚ) * Rat.mul_den_eq_num (r j).1
  obtain ⟨D, hD, hz⟩ := hden
  choose z hz using hz
  have hpos (j : J) : 0 < z j := by
    have hp : (0 : ℚ) < (D : ℚ)*(r j).1 := mul_pos (by exact_mod_cast hD) (r j).property
    rw [hz j] at hp
    exact_mod_cast hp
  have hnat (j : J) : 0 < (z j).toNat := by
    have hc : (0 : ℤ) < ((z j).toNat : ℤ) := by
      rw [Int.toNat_of_nonneg (hpos j).le]
      exact hpos j
    exact_mod_cast hc
  refine ⟨D, hD, fun j => (z j).toNat, hnat, fun j => ?_⟩
  rw [hz j]
  exact_mod_cast (Int.toNat_of_nonneg (hpos j).le).symm

/-- Reparametrization of the real line acts on its complex-valued function algebra. -/
private def lineRescale (D : ℝ) : (ℝ → ℂ) →ₐ[ℂ] (ℝ → ℂ) where
  toFun F t := F (t/D)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

private theorem lineRescale_injective {D : ℝ} (hD : D ≠ 0) :
    Function.Injective (lineRescale D) := by
  intro F G h
  funext t
  have he := congrFun h (D*t)
  change F (D*t/D) = G (D*t/D) at he
  have ht : D*t/D = t := by field_simp [hD]
  simpa only [ht] using he

/-- Clearing denominators rescales each physical jet by its exact nonzero chain factor. -/
theorem jet_rescale (r : Dilation) {D m : ℕ} (hD : 0 < D) (hm : 0 < m)
    (hscale : (D : ℚ)*r.1 = m) (k : ℕ) (z : ℂ) :
    iteratedDeriv k (zetaDilation r) ((D : ℂ)*z) =
      ((D : ℂ)^k)⁻¹ * iteratedDeriv k (GammaJoint.zetaDilation (m-1)) z := by
  have hDc : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  have hc : (D : ℂ)*(r.1 : ℂ) = m := by exact_mod_cast hscale
  have hfun : (fun z : ℂ => zetaDilation r ((D : ℂ)*z)) =
      GammaJoint.zetaDilation (m-1) := by
    funext v
    change riemannZeta ((r.1 : ℂ)*((D : ℂ)*v)) =
      riemannZeta (((m-1+1 : ℕ) : ℂ)*v)
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm.ne')]
    congr 1
    rw [show (r.1 : ℂ)*((D : ℂ)*v) = ((D : ℂ)*(r.1 : ℂ))*v by ring, hc]
  have hd := congrArg (fun f : ℂ → ℂ => iteratedDeriv k f z) hfun
  rw [iteratedDeriv_comp_const_mul_of_ne _ _ hDc] at hd
  rw [← hd, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hDc), one_mul]

/-- The line `Re s=2D` becomes the existing integer-dilation line `Re z=2`. -/
theorem jet_line_eq (r : Dilation) {D m : ℕ} (hD : 0 < D) (hm : 0 < m)
    (hscale : (D : ℚ)*r.1 = m) (k : ℕ) (t : ℝ) :
    iteratedDeriv k (zetaDilation r) (((2*(D : ℝ) : ℝ) : ℂ)+t*I) =
      ((D : ℂ)^k)⁻¹ * iteratedDeriv k (GammaJoint.zetaDilation (m-1))
        (2+((t/(D : ℝ) : ℝ) : ℂ)*I) := by
  have hDc : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  have hz : (D : ℂ)*(2+((t/(D : ℝ) : ℝ) : ℂ)*I) =
      (((2*(D : ℝ) : ℝ) : ℂ)+t*I) := by
    push_cast
    field_simp [hDc]
  rw [← hz]
  exact jet_rescale r hD hm hscale k _

/-- A finite rational family has continuous almost-periodic jets on its own common line. -/
theorem jet_line (r : Dilation) {D m : ℕ} (hD : 0 < D) (hm : 0 < m)
    (hscale : (D : ℚ)*r.1 = m) (k : ℕ) :
    Continuous (fun t : ℝ => iteratedDeriv k (zetaDilation r) (((2*(D : ℝ) : ℝ) : ℂ)+t*I)) ∧
    _root_.HTGeometry.IsBohrAlmostPeriodic
      (fun t : ℝ => iteratedDeriv k (zetaDilation r) (((2*(D : ℝ) : ℝ) : ℂ)+t*I)) := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have h := GammaJoint.zetaDilation_jet_line (m-1) k
  have he : (fun t : ℝ => iteratedDeriv k (zetaDilation r) (((2*(D : ℝ) : ℝ) : ℂ)+t*I)) =
      fun t : ℝ => ((D : ℂ)^k)⁻¹ * iteratedDeriv k (GammaJoint.zetaDilation (m-1))
        (2+((t/(D : ℝ) : ℝ) : ℂ)*I) := funext (jet_line_eq r hD hm hscale k)
  rw [he]
  refine ⟨continuous_const.mul (h.1.comp (continuous_id.div_const (D : ℝ))), ?_⟩
  apply isBohrAlmostPeriodic_const_mul
  have ha := GammaJoint.bohr_comp_pos_mul h.2 (inv_pos.mpr hDr)
  simpa only [div_eq_mul_inv, mul_comm] using ha

/-- Exact reparametrization preserves independence of any finite packet of rational jets. -/
theorem jets_line_algebraicIndependent {J : Type*} (r : J → Dilation) (k : J → ℕ)
    {D : ℕ} (hD : 0 < D) (m : J → ℕ) (hm : ∀ j, 0 < m j)
    (hscale : ∀ j, (D : ℚ)*(r j).1 = m j)
    (hinj : Function.Injective (fun j => (m j-1, k j))) :
    AlgebraicIndependent ℂ (fun j => fun t : ℝ =>
      iteratedDeriv (k j) (zetaDilation (r j)) (((2*(D : ℝ) : ℝ) : ℂ)+t*I)) := by
  have hDr : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hDc : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  have hi := GammaJoint.zetaDilation_jets_line_algebraicIndependent.comp
    (fun j => (m j-1, k j)) hinj
  have hr := hi.map' (f := lineRescale (D : ℝ)) (lineRescale_injective hDr)
  have hs := AlgebraicIndependent.const_mul_coordinates hr
    (fun j => ((D : ℂ)^(k j))⁻¹) (fun j => inv_ne_zero (pow_ne_zero _ hDc))
  change AlgebraicIndependent ℂ (fun j => fun t : ℝ => ((D : ℂ)^(k j))⁻¹ *
    iteratedDeriv (k j) (GammaJoint.zetaDilation (m j-1)) (2+((t/(D : ℝ) : ℝ) : ℂ)*I)) at hs
  have he : (fun j => fun t : ℝ =>
      iteratedDeriv (k j) (zetaDilation (r j)) (((2*(D : ℝ) : ℝ) : ℂ)+t*I)) =
      fun j => fun t : ℝ => ((D : ℂ)^(k j))⁻¹ *
        iteratedDeriv (k j) (GammaJoint.zetaDilation (m j-1))
          (2+((t/(D : ℝ) : ℝ) : ℂ)*I) := by
    funext j t
    exact jet_line_eq (r j) hD (hm j) (hscale j) (k j) t
  rw [he]
  exact hs

/-- All positive rational dilates are jointly differentially independent over the actual Gamma field. -/
theorem zetaDilation_differentialIndependent_gamma :
    DifferentialIndependent ↥gammaCoefficientField zetaDilationMero := by
  change AlgebraicIndependent ↥gammaCoefficientField
    (fun p : Dilation × ℕ => differentialJet p.2 (zetaDilationMero p.1))
  apply (algebraicIndependent_iff_forall_finite_subfamily _).mpr
  intro S hS
  letI : Fintype S := hS.fintype
  obtain ⟨D, hD, m, hm, hscale⟩ := exists_positive_integer_scales (fun p : S => p.1.1)
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  have hinj : Function.Injective (fun p : S => (m p-1, p.1.2)) := by
    intro p q he
    have hmk := congrArg Prod.fst he
    have hk := congrArg Prod.snd he
    have hm' : m p = m q := by have := hm p; have := hm q; dsimp only at hmk; omega
    have hr : p.1.1 = q.1.1 := by
      apply Subtype.ext
      apply (mul_left_cancel₀ hDq)
      rw [hscale p, hscale q, hm']
    exact Subtype.ext (Prod.ext hr hk)
  have hσ : (0 : ℝ) < 2*(D : ℝ) := mul_pos (by norm_num) (by exact_mod_cast hD)
  have h := GammaJoint.algebraicIndependent_gamma_of_line hσ
    (fun p : S => (upperEndAnalyticDeriv^[p.1.2]) (zetaDilationAnalytic p.1.1))
    (fun p : S => iteratedDeriv p.1.2 (zetaDilation p.1.1))
    (fun p => upperEndAnalyticDeriv_iterate_repr p.1.2 (zetaDilationAnalytic p.1.1)
      (zetaDilation p.1.1) rfl)
    (fun p => (jet_line p.1.1 hD (hm p) (hscale p) p.1.2).1)
    (fun p => (jet_line p.1.1 hD (hm p) (hscale p) p.1.2).2)
    (jets_line_algebraicIndependent (fun p : S => p.1.1) (fun p : S => p.1.2)
      hD m hm hscale hinj)
  simpa only [zetaDilationMero, GaloisForLFunctions.HTGeometry.differentialJet_algebraMap] using h

/-- The concrete theta–Gamma coefficient field preserves full rational-dilation independence. -/
theorem zetaDilation_differentialIndependent_thetaGamma :
    DifferentialIndependent ↥ModularThetaCoefficients.thetaGammaCoefficientField zetaDilationMero :=
  (ModularThetaCoefficients.thetaGamma_differentialIndependent_iff _).mpr
    zetaDilation_differentialIndependent_gamma

/-- Positive rational powers remain among the actual dilation parameters. -/
def orbitDilation (q : Dilation) (j : ℕ) : Dilation := ⟨q.1^j, pow_pos q.property _⟩

/-- The actual rational Mahler orbit, including contracting rational multipliers. -/
def mahlerZetaMero (q : Dilation) (j : ℕ) : upperEndMeroField :=
  zetaDilationMero (orbitDilation q j)

theorem mahlerZetaMero_differentialIndependent (q : Dilation) (hq : q.1 ≠ 1) :
    DifferentialIndependent ↥ModularThetaCoefficients.thetaGammaCoefficientField
      (mahlerZetaMero q) := by
  have hinj : Function.Injective (orbitDilation q) := by
    intro j k he
    exact pow_right_injective₀ q.property hq (congrArg Subtype.val he)
  exact zetaDilation_differentialIndependent_thetaGamma.comp (orbitDilation q) hinj

/-- The unique degenerate positive rational multiplier is one, where every orbit coordinate repeats. -/
theorem mahlerZetaMero_differentialIndependent_iff (q : Dilation) :
    DifferentialIndependent ↥ModularThetaCoefficients.thetaGammaCoefficientField
      (mahlerZetaMero q) ↔ q.1 ≠ 1 := by
  constructor
  · intro h hq
    have ha : AlgebraicIndependent ↥ModularThetaCoefficients.thetaGammaCoefficientField
        (fun p : ℕ × ℕ => differentialJet p.2 (mahlerZetaMero q p.1)) := h
    have hi := ha.injective
    have he : differentialJet 0 (mahlerZetaMero q 0) = differentialJet 0 (mahlerZetaMero q 1) := by
      change zetaDilationMero (orbitDilation q 0) = zetaDilationMero (orbitDilation q 1)
      congr 1
      apply Subtype.ext
      simp only [orbitDilation, pow_zero, pow_one, hq]
    have hn : ((0, 0) : ℕ × ℕ) = (1, 0) := hi he
    exact Nat.zero_ne_one (congrArg Prod.fst hn)
  · exact mahlerZetaMero_differentialIndependent q

/-- No finite nonzero differential–Mahler polynomial over the concrete theta–Gamma field
vanishes for any positive rational multiplier other than one. -/
theorem mahlerZeta_no_polynomial_relation (q : Dilation) (hq : q.1 ≠ 1)
    (P : MvPolynomial (ℕ × ℕ) ↥ModularThetaCoefficients.thetaGammaCoefficientField)
    (hP : P ≠ 0) :
    MvPolynomial.aeval (fun p : ℕ × ℕ => differentialJet p.2 (mahlerZetaMero q p.1)) P ≠ 0 :=
  fun he => hP ((mahlerZetaMero_differentialIndependent q hq).eq_zero_of_aeval_eq_zero P he)

/-- The orbit is represented by the literal function `s ↦ ζ(q^j s)`. -/
theorem mahlerZeta_representative (q : Dilation) (j : ℕ) :
    upperEndAnalyticSubring.subtype (zetaDilationAnalytic (orbitDilation q j)) =
      Germ.coeRingHom upperEndFilter (fun s : ℂ => riemannZeta (((q.1 : ℂ)^j)*s)) := by
  apply Germ.coe_eq.mpr
  exact Eventually.of_forall fun s => by simp only [zetaDilation, orbitDilation, Rat.cast_pow]

#print axioms exists_positive_integer_scales
#print axioms jets_line_algebraicIndependent
#print axioms zetaDilation_differentialIndependent_gamma
#print axioms zetaDilation_differentialIndependent_thetaGamma
#print axioms mahlerZetaMero_differentialIndependent_iff
#print axioms mahlerZeta_no_polynomial_relation
#print axioms mahlerZeta_representative

end GaloisForLFunctions.ArithmeticHarmonicAnalysis.GammaRational
