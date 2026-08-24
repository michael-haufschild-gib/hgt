import GaloisForLFunctions.HTGeometry.FirstOrderConnectionGauge
import GaloisForLFunctions.HTGeometry.FreeMomentumSpectralClassification
import GaloisForLFunctions.QuantumAlg.Util.Complex
import GaloisForLFunctions.HTGeometry.SeparatedPointCount
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly

/-!
# Finite-interval classification of scalar-symbol first-order connections

Endpoint gauge transport reduces every locally integrable self-adjoint matrix potential to one
effective unitary holonomy. Its characteristic-polynomial roots give at most the fiber rank many
phase offsets, so every admitted energy lies in a finite union of equally spaced lattices. The
module also proves an explicit linear window count and rules out every positive eventual
`T * log T` lower density.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open Complex MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [FiniteDimensional ℂ E]

/-- Endpoint transport converts a boundary unitary into effective holonomy. -/
def effectiveBoundaryHolonomy
    (g0 gL W : E ≃ₗᵢ[ℂ] E) : E ≃ₗᵢ[ℂ] E :=
  g0.trans (W.trans gL.symm)

omit [CompleteSpace E] [FiniteDimensional ℂ E] in
@[simp]
theorem effectiveBoundaryHolonomy_apply
    (g0 gL W : E ≃ₗᵢ[ℂ] E) (x : E) :
    effectiveBoundaryHolonomy g0 gL W x = gL.symm (W (g0 x)) := rfl

omit [CompleteSpace E] [FiniteDimensional ℂ E] in
theorem transported_boundary_iff
    (g0 gL W : E ≃ₗᵢ[ℂ] E) (x y : E) :
    gL x = W (g0 y) ↔ x = effectiveBoundaryHolonomy g0 gL W y := by
  constructor
  · intro h
    have := congrArg gL.symm h
    simpa [effectiveBoundaryHolonomy] using this
  · intro h
    have := congrArg gL h
    simpa [effectiveBoundaryHolonomy] using this

/-- Effective endpoint holonomy of a locally integrable self-adjoint connection. -/
def connectionEffectiveHolonomy
    {c : ℝ} (hc : c ≠ 0)
    {V : ℝ → E →L[ℂ] E} (hV : LocallyIntegrable V volume)
    (hVstar : ∀ t, IsSelfAdjoint (V t)) (L : ℝ) (W : E ≃ₗᵢ[ℂ] E) :
    E ≃ₗᵢ[ℂ] E :=
  effectiveBoundaryHolonomy
    (caratheodoryGaugeUnitary hc hV hVstar 0)
    (caratheodoryGaugeUnitary hc hV hVstar L) W

/-- Exact endpoint gauge law, equation (7) of the card. -/
theorem caratheodoryGauge_boundary_iff_effectiveHolonomy
    {c : ℝ} (hc : c ≠ 0)
    {V : ℝ → E →L[ℂ] E} (hV : LocallyIntegrable V volume)
    (hVstar : ∀ t, IsSelfAdjoint (V t)) (L : ℝ) (W : E ≃ₗᵢ[ℂ] E)
    (g : ℝ → E) :
    caratheodoryGauge c V L (g L) = W (caratheodoryGauge c V 0 (g 0)) ↔
      g L = connectionEffectiveHolonomy hc hV hVstar L W (g 0) := by
  exact transported_boundary_iff
    (caratheodoryGaugeUnitary hc hV hVstar 0)
    (caratheodoryGaugeUnitary hc hV hVstar L) W (g L) (g 0)

/-- Free interval mode with energy `lam`. -/
def freeIntervalMode (c lam : ℝ) (v : E) (u : ℝ) : E :=
  Complex.exp (((((lam / c : ℝ) : ℂ) * (u : ℂ))) * Complex.I) • v

omit [CompleteSpace E] [FiniteDimensional ℂ E] in
@[simp]
theorem freeIntervalMode_zero (c lam : ℝ) (v : E) :
    freeIntervalMode c lam v 0 = v := by
  simp [freeIntervalMode]

omit [CompleteSpace E] [FiniteDimensional ℂ E] in
theorem hasDerivAt_freeIntervalMode
    {c : ℝ} (lam : ℝ) (v : E) (u : ℝ) :
    HasDerivAt (freeIntervalMode c lam v)
      ((((lam / c : ℝ) : ℂ) * Complex.I) • freeIntervalMode c lam v u) u := by
  have hinner : HasDerivAt
      (fun t : ℝ => (((lam / c : ℝ) : ℂ) * (t : ℂ)) * Complex.I)
      (((lam / c : ℝ) : ℂ) * Complex.I) u := by
    simpa only [id_eq, ofReal_one, mul_one] using
      ((HasDerivAt.ofReal_comp (hasDerivAt_id u)).const_mul
        ((lam / c : ℝ) : ℂ)).mul_const Complex.I
  have hexp := (Complex.hasDerivAt_exp _).comp u hinner
  have hsmul := hexp.smul_const v
  change HasDerivAt
    (fun y : ℝ => Complex.exp (((lam / c : ℝ) : ℂ) * (y : ℂ) * Complex.I) • v)
    ((((lam / c : ℝ) : ℂ) * Complex.I) •
      (Complex.exp (((lam / c : ℝ) : ℂ) * (u : ℂ) * Complex.I) • v)) u
  simpa only [Function.comp_apply, smul_smul, mul_comm, mul_left_comm, mul_assoc] using hsmul

omit [CompleteSpace E] [FiniteDimensional ℂ E] in
/-- The free mode solves `-ic g' = lam g` pointwise. -/
theorem freeIntervalMode_eigen_equation
    {c : ℝ} (hc : c ≠ 0) (lam : ℝ) (v : E) (u : ℝ) :
    (-Complex.I * (c : ℂ)) •
        ((((lam / c : ℝ) : ℂ) * Complex.I) • freeIntervalMode c lam v u) =
      (lam : ℂ) • freeIntervalMode c lam v u := by
  rw [smul_smul]
  congr 1
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  push_cast
  field_simp [hcC]
  rw [Complex.I_sq]
  ring

def unitaryEndomorphism (U : E ≃ₗᵢ[ℂ] E) : Module.End ℂ E :=
  U.toLinearEquiv.toLinearMap

noncomputable def unitaryEigenvalues (U : E ≃ₗᵢ[ℂ] E) : Finset ℂ :=
  (unitaryEndomorphism U).charpoly.roots.toFinset

omit [CompleteSpace E] in
theorem mem_unitaryEigenvalues_iff (U : E ≃ₗᵢ[ℂ] E) (z : ℂ) :
    z ∈ unitaryEigenvalues U ↔ ∃ v : E, v ≠ 0 ∧ U v = z • v := by
  classical
  have hchar : (unitaryEndomorphism U).charpoly ≠ 0 :=
    (LinearMap.charpoly_monic (unitaryEndomorphism U)).ne_zero
  rw [unitaryEigenvalues, Multiset.mem_toFinset, Polynomial.mem_roots hchar,
    ← Module.End.hasEigenvalue_iff_isRoot_charpoly]
  constructor
  · intro hz
    rw [Module.End.hasEigenvalue_iff, Submodule.ne_bot_iff] at hz
    obtain ⟨v, hv, hv0⟩ := hz
    exact ⟨v, hv0, Module.End.mem_eigenspace_iff.mp hv⟩
  · rintro ⟨v, hv0, hv⟩
    rw [Module.End.hasEigenvalue_iff, Submodule.ne_bot_iff]
    exact ⟨v, Module.End.mem_eigenspace_iff.mpr hv, hv0⟩

omit [CompleteSpace E] in
theorem card_unitaryEigenvalues_le_finrank (U : E ≃ₗᵢ[ℂ] E) :
    (unitaryEigenvalues U).card ≤ Module.finrank ℂ E := by
  classical
  calc
    (unitaryEigenvalues U).card ≤ (unitaryEndomorphism U).charpoly.roots.card :=
      Multiset.toFinset_card_le _
    _ ≤ (unitaryEndomorphism U).charpoly.natDegree := Polynomial.card_roots' _
    _ = Module.finrank ℂ E := LinearMap.charpoly_natDegree _

omit [CompleteSpace E] in
theorem norm_eq_one_of_mem_unitaryEigenvalues
    (U : E ≃ₗᵢ[ℂ] E) {z : ℂ} (hz : z ∈ unitaryEigenvalues U) : ‖z‖ = 1 := by
  obtain ⟨v, hv0, hv⟩ := (mem_unitaryEigenvalues_iff U z).mp hz
  have hnormU : ‖U v‖ = ‖v‖ := U.norm_map v
  rw [hv, norm_smul] at hnormU
  have hnorm : ‖z‖ * ‖v‖ = 1 * ‖v‖ := by
    simpa using hnormU
  exact mul_right_cancel₀ (norm_ne_zero_iff.mpr hv0) hnorm

noncomputable def unitaryEigenphases (U : E ≃ₗᵢ[ℂ] E) : Finset ℝ :=
  (unitaryEigenvalues U).image Complex.arg

omit [CompleteSpace E] in
theorem card_unitaryEigenphases_le_finrank (U : E ≃ₗᵢ[ℂ] E) :
    (unitaryEigenphases U).card ≤ Module.finrank ℂ E := by
  exact le_trans Finset.card_image_le (card_unitaryEigenvalues_le_finrank U)

omit [CompleteSpace E] in
theorem mem_unitaryEigenphases_bounds
    (U : E ≃ₗᵢ[ℂ] E) {theta : ℝ} (htheta : theta ∈ unitaryEigenphases U) :
    -Real.pi < theta ∧ theta ≤ Real.pi := by
  classical
  obtain ⟨z, _hz, rfl⟩ := Finset.mem_image.mp htheta
  exact ⟨Complex.neg_pi_lt_arg z, Complex.arg_le_pi z⟩

/-- Equality of scalar phases is precisely equality modulo `2*pi`. -/
theorem exp_real_mul_I_eq_exp_real_mul_I_iff
    (x theta : ℝ) :
    Complex.exp ((x : ℂ) * Complex.I) =
        Complex.exp ((theta : ℂ) * Complex.I) ↔
      ∃ k : ℤ, x = theta + 2 * Real.pi * (k : ℝ) := by
  constructor
  · intro h
    have hone : Complex.exp (((x - theta : ℝ) : ℂ) * Complex.I) = 1 := by
      rw [show (((x - theta : ℝ) : ℂ) * Complex.I) =
          (x : ℂ) * Complex.I + (-((theta : ℂ) * Complex.I)) by push_cast; ring,
        Complex.exp_add, Complex.exp_neg, h]
      exact mul_inv_cancel₀ (Complex.exp_ne_zero _)
    obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp hone
    refine ⟨k, ?_⟩
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    have hcast : ((x - theta : ℝ) : ℂ) = ((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) := by
      apply mul_right_cancel₀ hI
      calc
        ((x - theta : ℝ) : ℂ) * Complex.I =
            (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := hk
        _ = ((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) * Complex.I := by
          push_cast
          ring
    have hr : x - theta = 2 * Real.pi * (k : ℝ) := Complex.ofReal_injective hcast
    linarith
  · rintro ⟨k, rfl⟩
    rw [show (((theta + 2 * Real.pi * (k : ℝ) : ℝ) : ℂ) * Complex.I) =
        (theta : ℂ) * Complex.I + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by
      push_cast
      ring,
      Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I]
    simp

theorem exp_interval_phase_eq_iff_lattice
    {c L : ℝ} (hc : c ≠ 0) (hL : L ≠ 0) (lam theta : ℝ) :
    Complex.exp ((((lam * L / c : ℝ) : ℂ)) * Complex.I) =
        Complex.exp ((theta : ℂ) * Complex.I) ↔
      ∃ k : ℤ, lam = (c / L) * (theta + 2 * Real.pi * (k : ℝ)) := by
  rw [exp_real_mul_I_eq_exp_real_mul_I_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    field_simp [hc, hL] at hk ⊢
    nlinarith
  · rintro ⟨k, rfl⟩
    refine ⟨k, ?_⟩
    field_simp [hc, hL]

def intervalEigenEnergySet (c L : ℝ) (U : E ≃ₗᵢ[ℂ] E) : Set ℝ :=
  {lam | ∃ v : E, v ≠ 0 ∧
    U v = Complex.exp ((((lam * L / c : ℝ) : ℂ)) * Complex.I) • v}

def phaseEnergyLattice (c L theta : ℝ) : Set ℝ :=
  {lam | ∃ k : ℤ, lam = (c / L) * (theta + 2 * Real.pi * (k : ℝ))}

omit [CompleteSpace E] in
/-- Exact finite-dimensional interval spectrum: at most `finrank E` phase lattices. -/
theorem intervalEigenEnergySet_eq_biUnion_phaseLattices
    {c L : ℝ} (hc : c ≠ 0) (hL : L ≠ 0) (U : E ≃ₗᵢ[ℂ] E) :
    intervalEigenEnergySet c L U =
      ⋃ theta ∈ unitaryEigenphases U, phaseEnergyLattice c L theta := by
  ext lam
  constructor
  · rintro ⟨v, hv0, hv⟩
    let z : ℂ := Complex.exp ((((lam * L / c : ℝ) : ℂ)) * Complex.I)
    have hz : z ∈ unitaryEigenvalues U :=
      (mem_unitaryEigenvalues_iff U z).mpr ⟨v, hv0, hv⟩
    have hphase : Complex.exp ((Complex.arg z : ℂ) * Complex.I) = z :=
      QuantumAlg.exp_arg_of_norm_eq_one z
        (norm_eq_one_of_mem_unitaryEigenvalues U hz)
    have hlat : lam ∈ phaseEnergyLattice c L (Complex.arg z) := by
      apply (exp_interval_phase_eq_iff_lattice hc hL lam (Complex.arg z)).mp
      exact hphase.symm
    exact Set.mem_iUnion₂.mpr ⟨Complex.arg z,
      Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨z, hz, rfl⟩), hlat⟩
  · intro hlam
    obtain ⟨theta, htheta, hlat⟩ := Set.mem_iUnion₂.mp hlam
    have htheta' : theta ∈ unitaryEigenphases U := Finset.mem_coe.mp htheta
    obtain ⟨z, hz, harg⟩ := Finset.mem_image.mp htheta'
    obtain ⟨v, hv0, hv⟩ := (mem_unitaryEigenvalues_iff U z).mp hz
    refine ⟨v, hv0, ?_⟩
    have hphase : Complex.exp ((Complex.arg z : ℂ) * Complex.I) = z :=
      QuantumAlg.exp_arg_of_norm_eq_one z
        (norm_eq_one_of_mem_unitaryEigenvalues U hz)
    have hexp := (exp_interval_phase_eq_iff_lattice hc hL lam theta).mpr hlat
    rw [← harg] at hexp
    rw [hv]
    congr 1
    exact (hexp.trans hphase).symm

/-- Positive spacing of every energy lattice. -/
def phaseLatticeSpacing (c L : ℝ) : ℝ :=
  |(c / L) * (2 * Real.pi)|

theorem phaseLatticeSpacing_pos
    {c L : ℝ} (hc : c ≠ 0) (hL : L ≠ 0) :
    0 < phaseLatticeSpacing c L := by
  rw [phaseLatticeSpacing, abs_pos]
  exact mul_ne_zero (div_ne_zero hc hL) (mul_ne_zero (by norm_num) Real.pi_ne_zero)

theorem phaseEnergyLattice_separated
    (c L theta : ℝ)
    {x y : ℝ} (hx : x ∈ phaseEnergyLattice c L theta)
    (hy : y ∈ phaseEnergyLattice c L theta) (hxy : x ≠ y) :
    phaseLatticeSpacing c L ≤ |x - y| := by
  obtain ⟨k, rfl⟩ := hx
  obtain ⟨l, rfl⟩ := hy
  have hkl : k ≠ l := by
    intro h
    apply hxy
    rw [h]
  have hdiff : k - l ≠ 0 := sub_ne_zero.mpr hkl
  have honeZ : (1 : ℤ) ≤ |k - l| := Int.one_le_abs hdiff
  have hone : (1 : ℝ) ≤ |(((k - l : ℤ) : ℝ))| := by
    rw [← Int.cast_abs]
    exact_mod_cast honeZ
  have hform :
      (c / L) * (theta + 2 * Real.pi * (k : ℝ)) -
          (c / L) * (theta + 2 * Real.pi * (l : ℝ)) =
        ((c / L) * (2 * Real.pi)) * (((k - l : ℤ) : ℝ)) := by
    push_cast
    ring
  rw [hform, abs_mul, phaseLatticeSpacing]
  nlinarith [abs_nonneg ((c / L) * (2 * Real.pi))]

noncomputable def phaseLatticeSlice
    (S : Finset ℝ) (c L theta : ℝ) : Finset ℝ := by
  classical
  exact S.filter fun lam => lam ∈ phaseEnergyLattice c L theta

theorem card_phaseLatticeSlice_le
    {c L T : ℝ} (hc : c ≠ 0) (hL : L ≠ 0) (hT : 0 ≤ T)
    (S : Finset ℝ) (hwindow : ∀ lam ∈ S, lam ∈ Set.Icc (-T) T)
    (theta : ℝ) :
    ((phaseLatticeSlice S c L theta).card : ℝ) ≤
      2 * T / phaseLatticeSpacing c L + 1 := by
  have hsep : ∀ x ∈ phaseLatticeSlice S c L theta,
      ∀ y ∈ phaseLatticeSlice S c L theta, x ≠ y →
        phaseLatticeSpacing c L ≤ |x - y| := by
    intro x hx y hy hxy
    have hx' : x ∈ S ∧ x ∈ phaseEnergyLattice c L theta := by
      simpa [phaseLatticeSlice] using hx
    have hy' : y ∈ S ∧ y ∈ phaseEnergyLattice c L theta := by
      simpa [phaseLatticeSlice] using hy
    apply phaseEnergyLattice_separated c L theta
    · exact hx'.2
    · exact hy'.2
    · exact hxy
  have hsub : ∀ x ∈ phaseLatticeSlice S c L theta, x ∈ Set.Icc (-T) T := by
    intro x hx
    apply hwindow x
    have hx' : x ∈ S ∧ x ∈ phaseEnergyLattice c L theta := by
      simpa [phaseLatticeSlice] using hx
    exact hx'.1
  have hcount := card_le_of_separated_of_subset_Icc
    (phaseLatticeSpacing_pos hc hL) (by linarith) (phaseLatticeSlice S c L theta)
    hsep hsub
  have heq : (T - -T) / phaseLatticeSpacing c L + 1 =
      2 * T / phaseLatticeSpacing c L + 1 := by ring
  rw [← heq]
  exact hcount

omit [CompleteSpace E] in
/-- Every finite spectral window has a linear counting bound. This is the precise `O(T)` content
of the finite-channel interval classification. -/
theorem card_finset_intervalEigenEnergySet_le
    {c L T : ℝ} (hc : c ≠ 0) (hL : L ≠ 0) (hT : 0 ≤ T)
    (U : E ≃ₗᵢ[ℂ] E) (S : Finset ℝ)
    (hspec : ∀ lam ∈ S, lam ∈ intervalEigenEnergySet c L U)
    (hwindow : ∀ lam ∈ S, lam ∈ Set.Icc (-T) T) :
    (S.card : ℝ) ≤
      ((unitaryEigenphases U).card : ℝ) *
        (2 * T / phaseLatticeSpacing c L + 1) := by
  classical
  let P := unitaryEigenphases U
  let A : ℝ → Finset ℝ := fun theta => phaseLatticeSlice S c L theta
  have hcover : S ⊆ P.biUnion A := by
    intro lam hlam
    have hspec' := hspec lam hlam
    rw [intervalEigenEnergySet_eq_biUnion_phaseLattices hc hL U] at hspec'
    obtain ⟨theta, htheta, hlat⟩ := Set.mem_iUnion₂.mp hspec'
    apply Finset.mem_biUnion.mpr
    refine ⟨theta, Finset.mem_coe.mp htheta, ?_⟩
    simpa [A, phaseLatticeSlice] using (Finset.mem_filter.mpr ⟨hlam, hlat⟩)
  have hcard : S.card ≤ (P.biUnion A).card := Finset.card_le_card hcover
  have hbi : (P.biUnion A).card ≤ ∑ theta ∈ P, (A theta).card :=
    Finset.card_biUnion_le
  have hslice : ∀ theta ∈ P,
      ((A theta).card : ℝ) ≤ 2 * T / phaseLatticeSpacing c L + 1 := by
    intro theta _
    exact card_phaseLatticeSlice_le hc hL hT S hwindow theta
  calc
    (S.card : ℝ) ≤ ((P.biUnion A).card : ℝ) := by exact_mod_cast hcard
    _ ≤ ∑ theta ∈ P, ((A theta).card : ℝ) := by exact_mod_cast hbi
    _ ≤ ∑ _theta ∈ P, (2 * T / phaseLatticeSpacing c L + 1) :=
      Finset.sum_le_sum hslice
    _ = ((P.card : ℕ) : ℝ) * (2 * T / phaseLatticeSpacing c L + 1) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ = ((unitaryEigenphases U).card : ℝ) *
        (2 * T / phaseLatticeSpacing c L + 1) := rfl

omit [CompleteSpace E] in
/-- Rank-only form of the linear interval count. -/
theorem card_finset_intervalEigenEnergySet_le_finrank
    {c L T : ℝ} (hc : c ≠ 0) (hL : L ≠ 0) (hT : 0 ≤ T)
    (U : E ≃ₗᵢ[ℂ] E) (S : Finset ℝ)
    (hspec : ∀ lam ∈ S, lam ∈ intervalEigenEnergySet c L U)
    (hwindow : ∀ lam ∈ S, lam ∈ Set.Icc (-T) T) :
    (S.card : ℝ) ≤
      (Module.finrank ℂ E : ℝ) *
        (2 * T / phaseLatticeSpacing c L + 1) := by
  have hcount := card_finset_intervalEigenEnergySet_le hc hL hT U S hspec hwindow
  have hphase : ((unitaryEigenphases U).card : ℝ) ≤ Module.finrank ℂ E := by
    exact_mod_cast card_unitaryEigenphases_le_finrank U
  have hfactor : 0 ≤ 2 * T / phaseLatticeSpacing c L + 1 := by
    have hdiv : 0 ≤ 2 * T / phaseLatticeSpacing c L :=
      div_nonneg (mul_nonneg (by norm_num) hT) (phaseLatticeSpacing_pos hc hL).le
    linarith
  exact hcount.trans (mul_le_mul_of_nonneg_right hphase hfactor)

omit [CompleteSpace E] in
/-- No family of genuine finite spectral windows can have a positive `T * log T` lower density.
This is the exact incompatibility with Riemann--von Mangoldt growth. -/
theorem not_eventually_T_mul_log_lower_for_intervalEigenEnergyFinsets
    {c L : ℝ} (hc : c ≠ 0) (hL : L ≠ 0) (U : E ≃ₗᵢ[ℂ] E)
    (F : ℝ → Finset ℝ)
    (hspec : ∀ T, 0 ≤ T → ∀ lam ∈ F T, lam ∈ intervalEigenEnergySet c L U)
    (hwindow : ∀ T, 0 ≤ T → ∀ lam ∈ F T, lam ∈ Set.Icc (-T) T)
    {rho : ℝ} (hrho : 0 < rho) :
    ¬ ∀ᶠ T : ℝ in Filter.atTop,
      rho * T * Real.log T ≤ ((F T).card : ℝ) := by
  intro hlower
  let M : ℝ := Module.finrank ℂ E
  let D : ℝ := phaseLatticeSpacing c L
  let A : ℝ := M * (2 / D + 1)
  have hD : 0 < D := phaseLatticeSpacing_pos hc hL
  have hM : 0 ≤ M := by positivity
  have hlog := Real.tendsto_log_atTop.eventually_gt_atTop (A / rho)
  obtain ⟨T, hlowerT, hlogT, hT⟩ :=
    (hlower.and (hlog.and (Filter.eventually_ge_atTop (1 : ℝ)))).exists
  have hT0 : 0 ≤ T := le_trans (by norm_num) hT
  have hcount := card_finset_intervalEigenEnergySet_le_finrank
    hc hL hT0 U (F T) (hspec T hT0) (hwindow T hT0)
  have hinner : 2 * T / D + 1 ≤ (2 / D + 1) * T := by
    have hrewrite : 2 * T / D = (2 / D) * T := by ring
    rw [hrewrite]
    nlinarith
  have hlinear : M * (2 * T / D + 1) ≤ A * T := by
    dsimp only [A]
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hinner hM
  have hAlog : A < Real.log T * rho := (div_lt_iff₀ hrho).mp hlogT
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hT
  have hstrict : A * T < rho * T * Real.log T := by
    have hmul := mul_lt_mul_of_pos_right hAlog hTpos
    nlinarith
  have : rho * T * Real.log T < rho * T * Real.log T :=
    lt_of_le_of_lt (hlowerT.trans (hcount.trans hlinear)) hstrict
  exact (lt_irrefl _ this)

/-- Closed finite-channel interval classification, including the holonomy formula, at most `m`
lattices, the uniform linear count, and the `T log T` obstruction. -/
theorem finiteChannel_connection_interval_classification
    (m : ℕ) {c L : ℝ} (hc : c ≠ 0) (hL : 0 < L)
    {V : ℝ → FiniteChannelFiber m →L[ℂ] FiniteChannelFiber m}
    (hV : LocallyIntegrable V volume) (hVstar : ∀ t, IsSelfAdjoint (V t))
    (W : FiniteChannelFiber m ≃ₗᵢ[ℂ] FiniteChannelFiber m) :
    let U := connectionEffectiveHolonomy hc hV hVstar L W
    (∀ g : ℝ → FiniteChannelFiber m,
      caratheodoryGauge c V L (g L) = W (caratheodoryGauge c V 0 (g 0)) ↔
        g L = U (g 0)) ∧
    (unitaryEigenphases U).card ≤ m ∧
    intervalEigenEnergySet c L U =
      ⋃ theta ∈ unitaryEigenphases U, phaseEnergyLattice c L theta ∧
    (∀ (T : ℝ), 0 ≤ T → ∀ S : Finset ℝ,
      (∀ lam ∈ S, lam ∈ intervalEigenEnergySet c L U) →
      (∀ lam ∈ S, lam ∈ Set.Icc (-T) T) →
      (S.card : ℝ) ≤ (m : ℝ) * (2 * T / phaseLatticeSpacing c L + 1)) ∧
    (∀ (F : ℝ → Finset ℝ),
      (∀ T, 0 ≤ T → ∀ lam ∈ F T, lam ∈ intervalEigenEnergySet c L U) →
      (∀ T, 0 ≤ T → ∀ lam ∈ F T, lam ∈ Set.Icc (-T) T) →
      ∀ {rho : ℝ}, 0 < rho →
        ¬ ∀ᶠ T : ℝ in Filter.atTop,
          rho * T * Real.log T ≤ ((F T).card : ℝ)) := by
  dsimp only
  refine ⟨fun g => caratheodoryGauge_boundary_iff_effectiveHolonomy
      hc hV hVstar L W g, ?_, ?_, ?_, ?_⟩
  · simpa using card_unitaryEigenphases_le_finrank
      (connectionEffectiveHolonomy hc hV hVstar L W)
  · exact intervalEigenEnergySet_eq_biUnion_phaseLattices hc hL.ne'
      (connectionEffectiveHolonomy hc hV hVstar L W)
  · intro T hT S hspec hwindow
    simpa using card_finset_intervalEigenEnergySet_le_finrank hc hL.ne' hT
      (connectionEffectiveHolonomy hc hV hVstar L W) S hspec hwindow
  · intro F hspec hwindow rho hrho
    exact not_eventually_T_mul_log_lower_for_intervalEigenEnergyFinsets hc hL.ne'
      (connectionEffectiveHolonomy hc hV hVstar L W) F hspec hwindow hrho

end GaloisForLFunctions.HTGeometry
