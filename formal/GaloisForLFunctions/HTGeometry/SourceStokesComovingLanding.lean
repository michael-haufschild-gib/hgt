import GaloisForLFunctions.HTGeometry.QuantileBurnolLanding
import GaloisForLFunctions.HTGeometry.EntireDet2HilbertSchmidtContinuity
import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesWallRealZeroClosure

/-!
# The comoving landing of the prime Stokes unit

For `d > 0` let `μ_d` be the atomic wall law carrying mass `π_d(p)` at `x_d(p) = 2d log p`, and
`Q_d` its quantile.  The normalized atoms `π_d(p)^{-1/2} 1_{x_d(p)}` form a Hilbert basis of
`L²(μ_d)`, so `J_d e_p = π_d(p)^{-1/2} 1_{x_d(p)}` is a unitary `ℓ²(Primes) → L²(μ_d)`, and the
comoving chart `U_d = (f ↦ f ∘ Q_d) J_d : ℓ²(Primes) → L²(0, 1)` is an isometry.

* **(SCIN.14)** `N_d = J_d* K_d J_d` for the wall kernel `K_d` of `κ` on `L²(μ_d)`, because
  `κ(x_d p, x_d q) = κ(log p, log q)`; hence `U_d T(d) U_d* = A_d` and `U_d T(-d) U_d* = -A_d`.
* **(SCIN.15)** `‖A_d - A_0‖₁ → 0`, so both chambers land in trace norm at `±A_0`.
* **(SCIN.16)** Conjugation by an isometry preserves every trace power, so
  `det(1 + z U_d T(d) U_d*) = det(1 + z N_d)`; the truncations of `N_d` to finite prime sets give
  the complete ordered prime-tuple Fredholm series of the wall law, and
  `det(1 + z U_d T(±d) U_d*) → det(1 ± z A_0)` locally uniformly in `z`.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory ContinuousLinearMap
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

/-! ## Operators determined by their matrix -/

theorem ext_hilbertBasis_inner {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (b : HilbertBasis ι ℂ E) {A B : E →L[ℂ] E}
    (h : ∀ i j, ⟪b i, A (b j)⟫_ℂ = ⟪b i, B (b j)⟫_ℂ) : A = B := by
  refine ContinuousLinearMap.ext_on (s := Set.range b)
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span) ?_
  rintro _ ⟨j, rfl⟩
  apply b.repr.injective
  ext i
  rw [HilbertBasis.repr_apply_apply, HilbertBasis.repr_apply_apply]
  exact h i j

/-! ## Trace powers under isometric conjugation -/

section Conjugation

variable {H H' K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem conj_pow_succ {U : H →L[ℂ] H'} (hU : adjoint U ∘L U = ContinuousLinearMap.id ℂ H)
    (T : H →L[ℂ] H) (n : ℕ) :
    (U ∘L T ∘L adjoint U) ^ (n + 1) = U ∘L (T ^ (n + 1)) ∘L adjoint U := by
  induction n with
  | zero => simp only [zero_add, pow_one]
  | succ n ih =>
    rw [pow_succ (U ∘L T ∘L adjoint U) (n + 1), ih, pow_succ T (n + 1),
      ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def]
    have h : adjoint U ∘L U ∘L T ∘L adjoint U = T ∘L adjoint U := by
      rw [← ContinuousLinearMap.comp_assoc, hU, ContinuousLinearMap.id_comp]
    simp only [ContinuousLinearMap.comp_assoc]
    rw [h]

/-- **Isometric conjugation preserves trace powers.**  If `U* U = 1` and `T = V* V` with `V`
Hilbert–Schmidt, then `tr (U T U*)^{n+1} = tr T^{n+1}`. -/
theorem opTrace_conj_pow_succ {U : H →L[ℂ] H'} (hU : adjoint U ∘L U = ContinuousLinearMap.id ℂ H)
    {V : H →L[ℂ] K} (hV : IsHilbertSchmidt V) (n : ℕ) :
    opTrace ((U ∘L (adjoint V ∘L V) ∘L adjoint U) ^ (n + 1))
      = opTrace ((adjoint V ∘L V) ^ (n + 1)) := by
  set T := adjoint V ∘L V
  have hT : T ^ (n + 1) = ((T ^ n) ∘L adjoint V) ∘L V := by
    rw [pow_succ, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc]
  rw [conj_pow_succ hU, hT]
  have h1 : U ∘L (((T ^ n) ∘L adjoint V) ∘L V) ∘L adjoint U
      = (U ∘L (T ^ n) ∘L adjoint V) ∘L (V ∘L adjoint U) := by
    simp only [ContinuousLinearMap.comp_assoc]
  have hA : IsHilbertSchmidt (U ∘L (T ^ n) ∘L adjoint V) :=
    (hV.adjoint.comp_left (T ^ n)).comp_left U
  have hB : IsHilbertSchmidt (V ∘L adjoint U) := hV.comp_right _
  rw [h1, opTrace_comp_comm hA hB, opTrace_comp_comm (hV.adjoint.comp_left (T ^ n)) hV]
  have h2 : (V ∘L adjoint U) ∘L U ∘L (T ^ n) ∘L adjoint V = V ∘L (T ^ n) ∘L adjoint V := by
    rw [ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc (adjoint U), hU,
      ContinuousLinearMap.id_comp]
  rw [h2]

end Conjugation

/-! ## The atomic wall law -/

section Atomic

variable {d : ℝ}

theorem wallLogCoordinate_injective (hd : 0 < d) :
    Function.Injective (routePPrimitiveGammaJuliaStokesWallLogCoordinate d) := by
  intro p q h
  simp only [routePPrimitiveGammaJuliaStokesWallLogCoordinate] at h
  have hlog : Real.log (p : ℝ) = Real.log (q : ℝ) :=
    mul_left_cancel₀ (show 2 * d ≠ 0 by positivity) h
  have hp : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.prop.pos
  have hq : (0 : ℝ) < (q : ℕ) := by exact_mod_cast q.prop.pos
  have hpq := Real.log_injOn_pos (Set.mem_Ioi.mpr hp) (Set.mem_Ioi.mpr hq) hlog
  exact Subtype.ext (by exact_mod_cast hpq)

theorem wallHalfLineLaw_of_pos (hd : 0 < d) :
    routePPrimitiveGammaJuliaStokesWallHalfLineLaw d
      = weightedPointLaw (routePPrimitiveGammaJuliaStokesWallLogCoordinate d)
          (fun p => ENNReal.ofReal (stokesWeight d p)) := by
  rw [routePPrimitiveGammaJuliaStokesWallHalfLineLaw, if_pos hd]
  rfl

/-- The atom at `x_d(p)` carries mass `π_d(p)`. -/
theorem wallHalfLineLaw_atom (hd : 0 < d) (p : Nat.Primes) :
    routePPrimitiveGammaJuliaStokesWallHalfLineLaw d
        {routePPrimitiveGammaJuliaStokesWallLogCoordinate d p}
      = ENNReal.ofReal (stokesWeight d p) := by
  rw [wallHalfLineLaw_of_pos hd, weightedPointLaw_apply _ _ (measurableSet_singleton _),
    tsum_eq_single p]
  · rw [Set.indicator_of_mem (Set.mem_singleton _)]
  · intro q hq
    exact Set.indicator_of_notMem
      (fun h => hq (wallLogCoordinate_injective hd (Set.mem_singleton_iff.mp h))) _

theorem wallHalfLineLaw_real_atom (hd : 0 < d) (p : Nat.Primes) :
    (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d).real
        {routePPrimitiveGammaJuliaStokesWallLogCoordinate d p} = stokesWeight d p := by
  rw [measureReal_def, wallHalfLineLaw_atom hd, ENNReal.toReal_ofReal (stokesWeight_pos hd p).le]

/-- The atomic law is carried by its atoms. -/
theorem ae_wallHalfLineLaw_of_atoms (hd : 0 < d) {P : ℝ → Prop} (hP : MeasurableSet {x | P x})
    (h : ∀ p, P (routePPrimitiveGammaJuliaStokesWallLogCoordinate d p)) :
    ∀ᵐ x ∂routePPrimitiveGammaJuliaStokesWallHalfLineLaw d, P x := by
  rw [wallHalfLineLaw_of_pos hd, weightedPointLaw, Measure.ae_sum_iff' hP]
  intro p
  refine Measure.ae_smul_measure ?_ _
  rw [ae_dirac_eq]
  exact Filter.eventually_pure.mpr (h p)

/-- Almost-everywhere equal functions agree at every atom. -/
theorem eq_at_atom_of_ae_eq (hd : 0 < d) {f g : ℝ → ℂ}
    (h : f =ᵐ[routePPrimitiveGammaJuliaStokesWallHalfLineLaw d] g) (p : Nat.Primes) :
    f (routePPrimitiveGammaJuliaStokesWallLogCoordinate d p)
      = g (routePPrimitiveGammaJuliaStokesWallLogCoordinate d p) := by
  by_contra hne
  have h0 := ae_iff.mp h
  have hle := (measure_mono (μ := routePPrimitiveGammaJuliaStokesWallHalfLineLaw d)
    (Set.singleton_subset_iff.mpr (show routePPrimitiveGammaJuliaStokesWallLogCoordinate d p ∈
      {a | ¬f a = g a} from hne))).trans (le_of_eq h0)
  rw [wallHalfLineLaw_atom hd, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at hle
  exact absurd hle (not_le.mpr (stokesWeight_pos hd p))

/-- The normalized atom `π_d(p)^{-1/2} 1_{x_d(p)}` of `L²(μ_d)`. -/
def wallAtomVector (d : ℝ) (p : Nat.Primes) :
    Lp ℂ 2 (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) :=
  (((Real.sqrt (stokesWeight d p))⁻¹ : ℝ) : ℂ) •
    indicatorConstLp 2
      (measurableSet_singleton (routePPrimitiveGammaJuliaStokesWallLogCoordinate d p))
      (measure_ne_top _ _) (1 : ℂ)

theorem wallAtomVector_ae (d : ℝ) (p : Nat.Primes) :
    (wallAtomVector d p : ℝ → ℂ) =ᵐ[routePPrimitiveGammaJuliaStokesWallHalfLineLaw d]
      fun x => (((Real.sqrt (stokesWeight d p))⁻¹ : ℝ) : ℂ) •
        ({routePPrimitiveGammaJuliaStokesWallLogCoordinate d p} : Set ℝ).indicator
          (fun _ => (1 : ℂ)) x := by
  unfold wallAtomVector
  filter_upwards [Lp.coeFn_smul (((Real.sqrt (stokesWeight d p))⁻¹ : ℝ) : ℂ)
    (indicatorConstLp 2 (measurableSet_singleton (routePPrimitiveGammaJuliaStokesWallLogCoordinate
      d p)) (measure_ne_top (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) _) (1 : ℂ)),
    indicatorConstLp_coeFn (hs := measurableSet_singleton
      (routePPrimitiveGammaJuliaStokesWallLogCoordinate d p))
      (hμs := measure_ne_top (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) _)
      (c := (1 : ℂ))] with x h1 h2
  rw [h1, Pi.smul_apply, h2]

theorem sqrt_stokesWeight_ne_zero (hd : 0 < d) (p : Nat.Primes) :
    ((Real.sqrt (stokesWeight d p) : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast (Real.sqrt_pos.mpr (stokesWeight_pos hd p)).ne'

theorem ofReal_stokesWeight_eq (d : ℝ) (p : Nat.Primes) (hd : 0 < d) :
    ((stokesWeight d p : ℝ) : ℂ)
      = ((Real.sqrt (stokesWeight d p) : ℝ) : ℂ) * ((Real.sqrt (stokesWeight d p) : ℝ) : ℂ) := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (stokesWeight_pos hd p).le]

/-- `⟪e_p, f⟫ = √π_d(p) f(x_d(p))`. -/
theorem inner_wallAtomVector (hd : 0 < d) (p : Nat.Primes)
    (f : Lp ℂ 2 (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d)) :
    ⟪wallAtomVector d p, f⟫_ℂ
      = ((Real.sqrt (stokesWeight d p) : ℝ) : ℂ)
        * f (routePPrimitiveGammaJuliaStokesWallLogCoordinate d p) := by
  rw [wallAtomVector, inner_smul_left, L2.inner_indicatorConstLp_one, integral_singleton,
    wallHalfLineLaw_real_atom hd, Complex.conj_ofReal, Complex.real_smul,
    ofReal_stokesWeight_eq d p hd, Complex.ofReal_inv]
  field_simp [sqrt_stokesWeight_ne_zero hd p]

/-- `∫ g e_q dμ_d = √π_d(q) g(x_d(q))`. -/
theorem integral_mul_wallAtomVector (hd : 0 < d) (g : ℝ → ℂ) (q : Nat.Primes) :
    ∫ y, g y * (wallAtomVector d q : ℝ → ℂ) y ∂routePPrimitiveGammaJuliaStokesWallHalfLineLaw d
      = ((Real.sqrt (stokesWeight d q) : ℝ) : ℂ)
        * g (routePPrimitiveGammaJuliaStokesWallLogCoordinate d q) := by
  have hae : (fun y => g y * (wallAtomVector d q : ℝ → ℂ) y)
      =ᵐ[routePPrimitiveGammaJuliaStokesWallHalfLineLaw d]
        ({routePPrimitiveGammaJuliaStokesWallLogCoordinate d q} : Set ℝ).indicator
          (fun y => (((Real.sqrt (stokesWeight d q))⁻¹ : ℝ) : ℂ) * g y) := by
    filter_upwards [wallAtomVector_ae d q] with y hy
    rw [hy]
    by_cases h : y ∈ ({routePPrimitiveGammaJuliaStokesWallLogCoordinate d q} : Set ℝ)
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, smul_eq_mul, mul_one, mul_comm]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, smul_zero, mul_zero]
  rw [integral_congr_ae hae, integral_indicator (measurableSet_singleton _), integral_singleton,
    wallHalfLineLaw_real_atom hd, Complex.real_smul, ofReal_stokesWeight_eq d q hd,
    Complex.ofReal_inv]
  field_simp [sqrt_stokesWeight_ne_zero hd q]

theorem wallAtomVector_apply_atom (hd : 0 < d) (p q : Nat.Primes) :
    (wallAtomVector d q : ℝ → ℂ) (routePPrimitiveGammaJuliaStokesWallLogCoordinate d p)
      = if p = q then (((Real.sqrt (stokesWeight d q))⁻¹ : ℝ) : ℂ) else 0 := by
  rw [eq_at_atom_of_ae_eq hd (wallAtomVector_ae d q) p]
  by_cases hpq : p = q
  · subst hpq
    rw [Set.indicator_of_mem (Set.mem_singleton _), if_pos rfl, smul_eq_mul, mul_one]
  · rw [if_neg hpq, Set.indicator_of_notMem
      (fun h => hpq (wallLogCoordinate_injective hd (Set.mem_singleton_iff.mp h))), smul_zero]

theorem orthonormal_wallAtomVector (hd : 0 < d) : Orthonormal ℂ (wallAtomVector d) := by
  rw [orthonormal_iff_ite]
  intro p q
  rw [inner_wallAtomVector hd, wallAtomVector_apply_atom hd]
  by_cases hpq : p = q
  · subst hpq
    rw [if_pos rfl, if_pos rfl, Complex.ofReal_inv]
    exact mul_inv_cancel₀ (sqrt_stokesWeight_ne_zero hd p)
  · rw [if_neg hpq, if_neg hpq, mul_zero]

theorem orthogonal_span_wallAtomVector (hd : 0 < d) :
    (Submodule.span ℂ (Set.range (wallAtomVector d)))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro f hf
  have hzero : ∀ p, (f : ℝ → ℂ) (routePPrimitiveGammaJuliaStokesWallLogCoordinate d p) = 0 := by
    intro p
    have h := (Submodule.mem_orthogonal _ f).mp hf (wallAtomVector d p)
      (Submodule.subset_span ⟨p, rfl⟩)
    rw [inner_wallAtomVector hd] at h
    exact (mul_eq_zero.mp h).resolve_left (sqrt_stokesWeight_ne_zero hd p)
  refine Lp.eq_zero_iff_ae_eq_zero.mpr ?_
  exact ae_wallHalfLineLaw_of_atoms hd (P := fun x => (f : ℝ → ℂ) x = 0)
    ((Lp.stronglyMeasurable f).measurable (measurableSet_singleton 0)) hzero

/-- The atomic Hilbert basis of `L²(μ_d)`. -/
def wallAtomBasis (hd : 0 < d) :
    HilbertBasis Nat.Primes ℂ (Lp ℂ 2 (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d)) :=
  HilbertBasis.mkOfOrthogonalEqBot (orthonormal_wallAtomVector hd)
    (orthogonal_span_wallAtomVector hd)

theorem wallAtomBasis_apply (hd : 0 < d) (p : Nat.Primes) :
    wallAtomBasis hd p = wallAtomVector d p := by
  rw [wallAtomBasis, HilbertBasis.coe_mkOfOrthogonalEqBot]

/-- The prime chart `J_d : ℓ²(Primes) → L²(μ_d)`, `J_d e_p = π_d(p)^{-1/2} 1_{x_d(p)}`. -/
def primeAtomChart (hd : 0 < d) :
    PrimeHilbert →L[ℂ] Lp ℂ 2 (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) :=
  ((wallAtomBasis hd).repr.symm :
    PrimeHilbert →L[ℂ] Lp ℂ 2 (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d))

theorem primeAtomChart_basis (hd : 0 < d) (p : Nat.Primes) :
    primeAtomChart hd (HilbertSchmidt.lpBasis Nat.Primes p) = wallAtomVector d p := by
  rw [primeAtomChart, HilbertSchmidt.lpBasis_apply]
  change (wallAtomBasis hd).repr.symm (lp.single 2 p 1) = _
  rw [HilbertBasis.repr_symm_single, wallAtomBasis_apply]

theorem primeAtomChart_comp_adjoint (hd : 0 < d) :
    primeAtomChart hd ∘L adjoint (primeAtomChart hd) = ContinuousLinearMap.id ℂ _ := by
  rw [primeAtomChart, LinearIsometryEquiv.adjoint_eq_symm, LinearIsometryEquiv.symm_symm]
  ext1 x
  exact (wallAtomBasis hd).repr.symm_apply_apply x

theorem adjoint_primeAtomChart_comp (hd : 0 < d) :
    adjoint (primeAtomChart hd) ∘L primeAtomChart hd = ContinuousLinearMap.id ℂ _ := by
  rw [primeAtomChart, LinearIsometryEquiv.adjoint_eq_symm, LinearIsometryEquiv.symm_symm]
  ext1 x
  exact (wallAtomBasis hd).repr.apply_symm_apply x

/-- **The prime matrix in the atomic chart.**  `N_d = J_d* K_d J_d`. -/
theorem normalizedStokesUnit_eq_primeAtomChart (hd : 0 < d) :
    normalizedStokesUnit d = adjoint (primeAtomChart hd) ∘L
      (wallKernelOf (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d)).op ∘L
        primeAtomChart hd := by
  refine ext_hilbertBasis_inner (HilbertSchmidt.lpBasis Nat.Primes) fun p q => ?_
  rw [comp_apply, comp_apply, adjoint_inner_right, primeAtomChart_basis, primeAtomChart_basis,
    inner_wallAtomVector hd,
    eq_at_atom_of_ae_eq hd ((wallKernelOf _).op_coeFn (wallAtomVector d q)) p]
  change _ = _ * ∫ y, ((wallCubicKernel (routePPrimitiveGammaJuliaStokesWallLogCoordinate d p) y
    : ℝ) : ℂ) * (wallAtomVector d q : ℝ → ℂ) y ∂routePPrimitiveGammaJuliaStokesWallHalfLineLaw d
  rw [integral_mul_wallAtomVector hd, lpBasis_eq_lpBasisVec, inner_lpBasisVec,
    normalizedStokesUnit_basis_coord hd, normalizedStokesPrimeKernel_eq hd,
    wallCubicKernel, routePPrimitiveGammaJuliaStokesWallCubicKernel_logCoordinate_eq_primeLog hd,
    Real.sqrt_mul (stokesWeight_pos hd p).le]
  push_cast
  ring

end Atomic

/-! ## The comoving chart -/

section Chart

variable {d : ℝ}

/-- The comoving chart `U_d = (f ↦ f ∘ Q_d) J_d : ℓ²(Primes) → L²(0, 1)`. -/
def comovingChart (hd : 0 < d) : PrimeHilbert →L[ℂ] Lp ℂ 2 (volume.restrict (Ioo (0 : ℝ) 1)) :=
  compL2 (measurePreserving_quantile (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d)) ∘L
    primeAtomChart hd

/-- **(SCIN.12).**  `U_d e_p = (π_d(p)^{-1/2} 1_{x_d(p)}) ∘ Q_d`. -/
theorem comovingChart_basis (hd : 0 < d) (p : Nat.Primes) :
    comovingChart hd (HilbertSchmidt.lpBasis Nat.Primes p)
      = compL2 (measurePreserving_quantile (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d))
          (wallAtomVector d p) := by
  rw [comovingChart, comp_apply, primeAtomChart_basis]

/-- **(SCIN.12).**  `U_d` is an isometry. -/
theorem adjoint_comovingChart_comp (hd : 0 < d) :
    adjoint (comovingChart hd) ∘L comovingChart hd = ContinuousLinearMap.id ℂ PrimeHilbert := by
  rw [comovingChart, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc,
    ← ContinuousLinearMap.comp_assoc _ (compL2 _), adjoint_compL2_comp_compL2,
    ContinuousLinearMap.id_comp, adjoint_primeAtomChart_comp]

theorem norm_comovingChart_apply (hd : 0 < d) (a : PrimeHilbert) : ‖comovingChart hd a‖ = ‖a‖ := by
  rw [comovingChart, comp_apply, norm_compL2_apply, primeAtomChart]
  exact (wallAtomBasis hd).repr.symm.norm_map a

theorem stokesCubicUnit_of_pos (hd : 0 < d) : stokesCubicUnit d = normalizedStokesUnit d := by
  rw [stokesCubicUnit, Real.sign_of_pos hd, abs_of_pos hd, Complex.ofReal_one, one_smul]

/-- **(SCIN.14).**  `U_d T(d) U_d* = A_d`. -/
theorem comovingChart_conj_stokesCubicUnit (hd : 0 < d) :
    comovingChart hd ∘L stokesCubicUnit d ∘L adjoint (comovingChart hd) = wallLandingOp d := by
  rw [stokesCubicUnit_of_pos hd, normalizedStokesUnit_eq_primeAtomChart hd, wallLandingOp,
    quantileLandingOp_eq_conj, comovingChart, ContinuousLinearMap.adjoint_comp]
  have hJ : ∀ (R : Lp ℂ 2 (volume.restrict (Ioo (0 : ℝ) 1)) →L[ℂ]
      Lp ℂ 2 (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d)),
      primeAtomChart hd ∘L adjoint (primeAtomChart hd) ∘L R = R := fun R => by
    rw [← ContinuousLinearMap.comp_assoc, primeAtomChart_comp_adjoint hd,
      ContinuousLinearMap.id_comp]
  simp only [ContinuousLinearMap.comp_assoc]
  rw [hJ, hJ]

/-- The negative chamber lands at `-A_d`: `U_d T(-d) U_d* = -A_d`. -/
theorem comovingChart_conj_stokesCubicUnit_neg (hd : 0 < d) :
    comovingChart hd ∘L stokesCubicUnit (-d) ∘L adjoint (comovingChart hd) = -wallLandingOp d := by
  rw [stokesCubicUnit_neg, ContinuousLinearMap.neg_comp, ContinuousLinearMap.comp_neg,
    comovingChart_conj_stokesCubicUnit hd]

theorem isHilbertSchmidt_normalizedStokesUnit (hd : 0 < d) :
    IsHilbertSchmidt (normalizedStokesUnit d) := by
  rw [normalizedStokesUnit_eq_adjoint_comp hd]
  exact (commonRadialPrimeSynthesis_isHilbertSchmidt _).comp_left _

theorem opTrace_comovingChart_conj_pow (hd : 0 < d) (n : ℕ) :
    opTrace ((comovingChart hd ∘L normalizedStokesUnit d ∘L adjoint (comovingChart hd)) ^ (n + 1))
      = opTrace (normalizedStokesUnit d ^ (n + 1)) := by
  rw [normalizedStokesUnit_eq_adjoint_comp hd]
  exact opTrace_conj_pow_succ (adjoint_comovingChart_comp hd)
    (commonRadialPrimeSynthesis_isHilbertSchmidt _) n

/-- `tr A_d = 1` for `d > 0`. -/
theorem opTrace_wallLandingOp (hd : 0 < d) : opTrace (wallLandingOp d) = 1 := by
  have h := opTrace_comovingChart_conj_pow hd 0
  rw [zero_add, pow_one, pow_one, ← stokesCubicUnit_of_pos hd,
    comovingChart_conj_stokesCubicUnit hd, stokesCubicUnit_of_pos hd,
    opTrace_normalizedStokesUnit hd] at h
  exact h

/-- **(SCIN.15), both chambers.**  `U_d T(±d) U_d* → ±A_0` in trace norm as `d → 0⁺`. -/
theorem tendsto_traceNorm_comovingChart_conj :
    Tendsto (fun d => traceNorm (Lp ℂ 2 (volume.restrict (Ioo (0 : ℝ) 1)))
      (wallLandingOp d - quantileWallOperator)) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun d => traceNorm (Lp ℂ 2 (volume.restrict (Ioo (0 : ℝ) 1)))
      (-wallLandingOp d - -quantileWallOperator)) (𝓝[>] 0) (𝓝 0) := by
  refine ⟨tendsto_traceNorm_wallLandingOp_sub,
    tendsto_traceNorm_wallLandingOp_sub.congr fun d => ?_⟩
  rw [show -wallLandingOp d - -quantileWallOperator
      = (-1 : ℂ) • (wallLandingOp d - quantileWallOperator) by rw [neg_one_smul]; abel,
    traceNorm_smul, norm_neg, norm_one, one_mul]

end Chart

/-! ## Determinant landing -/

section Determinant

variable {d : ℝ}

theorem fredholmDetOp_smul_eq_detOneSub {ι E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] [DecidableEq ι] (b : HilbertBasis ι ℂ E)
    (X : E →L[ℂ] E) (z : ℂ) : fredholmDetOp b (z • X) = detOneSub b X (-z) := by
  rw [detOneSub, neg_smul, neg_neg]

/-- **Finite prime truncation.**  `det(1 + z N_d)` is the complete ordered prime-tuple Fredholm
series of the atomic wall law. -/
theorem fredholmDetOp_normalizedStokesUnit (hd : 0 < d) (z : ℂ) :
    fredholmDetOp (HilbertSchmidt.lpBasis Nat.Primes) (z • normalizedStokesUnit d)
      = routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
          (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) z := by
  set b := HilbertSchmidt.lpBasis Nat.Primes
  set N := normalizedStokesUnit d
  have hN : IsHilbertSchmidt N := isHilbertSchmidt_normalizedStokesUnit hd
  set K := coordMatrix b N
  have hblock : ∀ s : Finset Nat.Primes, HilbertSchmidt.blockMatrix K s
      = routePPrimitiveGammaJuliaStokesNormalizedChildFiniteBlock d s := by
    intro s
    ext p q
    rw [routePPrimitiveGammaJuliaStokesNormalizedChildFiniteBlock_apply hd]
    change coordMatrix b N ((p : Nat.Primes), (q : Nat.Primes)) = _
    rw [coordMatrix_apply,
      show b (p : Nat.Primes) = lpBasisVec (p : Nat.Primes) from lpBasis_eq_lpBasisVec _,
      inner_lpBasisVec, normalizedStokesUnit_basis_coord hd, normalizedStokesPrimeKernel_eq hd,
      Real.sqrt_mul (stokesWeight_pos hd _).le]
    rfl
  have htrace : ∀ s : Finset Nat.Primes,
      (routePPrimitiveGammaJuliaStokesNormalizedChildFiniteBlock d s).trace
        = ∑ p ∈ s, ((stokesWeight d p : ℝ) : ℂ) := by
    intro s
    rw [Matrix.trace, ← Finset.sum_coe_sort s]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Matrix.diag_apply, routePPrimitiveGammaJuliaStokesNormalizedChildFiniteBlock_apply hd,
      Real.mul_self_sqrt (wallNormalizedWeight_nonneg hd _),
      wallCubicKernel_self (Real.log_pos (by exact_mod_cast (p : Nat.Primes).prop.one_lt)),
      mul_one]
    rfl
  have hsum : Tendsto (fun s : Finset Nat.Primes => ∑ p ∈ s, ((stokesWeight d p : ℝ) : ℂ)) atTop
      (𝓝 1) := by
    have h : HasSum (fun p => stokesWeight d p) 1 := by
      have := (summable_wallNormalizedWeight hd).hasSum
      rwa [tsum_wallNormalizedWeight hd] at this
    have h' := Complex.hasSum_ofReal.mpr h
    rw [Complex.ofReal_one] at h'
    exact h'
  have h1 := tendsto_finiteDet2_entireDet2 (isHS_coordMatrix b hN) (-z)
  have h2 := tendsto_routePPrimitiveGammaJuliaStokesNormalizedChildFiniteDet hd z
  have h3 : Tendsto (fun s : Finset Nat.Primes => Complex.exp
      (-(z * (routePPrimitiveGammaJuliaStokesNormalizedChildFiniteBlock d s).trace))) atTop
      (𝓝 (Complex.exp (-(z * 1)))) := by
    simp_rw [htrace]
    exact (Complex.continuous_exp.tendsto _).comp ((hsum.const_mul z).neg)
  have h4 : Tendsto (fun s => finiteDet2 (-(HilbertSchmidt.blockMatrix K s)) (-z)) atTop
      (𝓝 (routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
        (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) z * Complex.exp (-(z * 1)))) := by
    refine (h2.mul h3).congr fun s => ?_
    rw [hblock, finiteDet2, neg_smul_neg, Matrix.trace_neg,
      routePPrimitiveGammaJuliaStokesNormalizedChildFiniteDet]
    ring_nf
  have heq := tendsto_nhds_unique h1 h4
  rw [fredholmDetOp_smul_eq_detOneSub, detOneSub_eq b hN, heq, opTrace_normalizedStokesUnit hd,
    mul_assoc, ← Complex.exp_add, show -(z * 1) + -(-z) * 1 = 0 by ring, Complex.exp_zero, mul_one]

/-- **Isometric invariance.**  `det(1 + z U_d T(d) U_d*) = det(1 + z N_d)`. -/
theorem fredholmDetOp_comovingChart_conj {ι : Type*} [DecidableEq ι]
    (b : HilbertBasis ι ℂ (Lp ℂ 2 (volume.restrict (Ioo (0 : ℝ) 1)))) (hd : 0 < d) (z : ℂ) :
    fredholmDetOp b (z • (comovingChart hd ∘L stokesCubicUnit d ∘L adjoint (comovingChart hd)))
      = routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
          (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) z := by
  have hN := isHilbertSchmidt_normalizedStokesUnit hd
  have hX : IsHilbertSchmidt (comovingChart hd ∘L normalizedStokesUnit d ∘L
      adjoint (comovingChart hd)) := (hN.comp_right _).comp_left _
  rw [stokesCubicUnit_of_pos hd, fredholmDetOp_smul_eq_detOneSub,
    detOneSub_eq_of_opTrace_pow_eq b (HilbertSchmidt.lpBasis Nat.Primes) hX hN
      (opTrace_comovingChart_conj_pow hd),
    ← fredholmDetOp_smul_eq_detOneSub, fredholmDetOp_normalizedStokesUnit hd]

theorem fredholmDetOp_wallLandingOp {ι : Type*} [DecidableEq ι]
    (b : HilbertBasis ι ℂ (Lp ℂ 2 (volume.restrict (Ioo (0 : ℝ) 1)))) (hd : 0 < d) (z : ℂ) :
    fredholmDetOp b (z • wallLandingOp d)
      = routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
          (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) z := by
  rw [← comovingChart_conj_stokesCubicUnit hd, fredholmDetOp_comovingChart_conj b hd]

theorem coordMatrix_sub {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [DecidableEq ι] (b : HilbertBasis ι ℂ E) (S T : E →L[ℂ] E) :
    coordMatrix b (S - T) = coordMatrix b S - coordMatrix b T := by
  funext p
  rw [Pi.sub_apply, coordMatrix_apply, coordMatrix_apply, coordMatrix_apply, sub_apply,
    inner_sub_right]

/-- The pointwise wall landing of the operator determinant. -/
theorem tendsto_fredholmDetOp_wallLandingOp {ι : Type*} [DecidableEq ι]
    (b : HilbertBasis ι ℂ (Lp ℂ 2 (volume.restrict (Ioo (0 : ℝ) 1)))) (z : ℂ) :
    Tendsto (fun d => fredholmDetOp b (z • wallLandingOp d)) (𝓝[>] 0)
      (𝓝 (fredholmDetOp b (z • quantileWallOperator))) := by
  have hA0 := isHilbertSchmidt_quantileWallOperator
  have hA : ∀ d, IsHilbertSchmidt (wallLandingOp d) := fun d => by
    rw [wallLandingOp, quantileLandingOp_eq_adjoint_comp]
    exact (isHilbertSchmidt_quantileBurnolSynthesis _).comp_left _
  have hdet : Tendsto (fun d => entireDet2 (coordMatrix b (wallLandingOp d)) (-z)) (𝓝[>] 0)
      (𝓝 (entireDet2 (coordMatrix b quantileWallOperator) (-z))) := by
    rw [Filter.tendsto_iff_seq_tendsto]
    intro x hx
    refine tendsto_entireDet2_of_hsNorm_sub_tendsto_zero _ _
      (fun n => isHS_coordMatrix b (hA (x n))) (isHS_coordMatrix b hA0) ?_ (-z)
    have hS := (tendsto_hsNorm_wallSynthesis_sub.comp hx).const_mul 2
    rw [mul_zero] at hS
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hS
      (fun n => Real.sqrt_nonneg _) fun n => ?_
    rw [← coordMatrix_sub]
    refine le_trans ?_ (hsNorm_wallLandingOp_sub_le (x n))
    exact Real.sqrt_le_sqrt (hsNormSq_coordMatrix_le b ((hA (x n)).sub hA0))
  have hev : ∀ᶠ d in 𝓝[>] (0 : ℝ), fredholmDetOp b (z • wallLandingOp d)
      = entireDet2 (coordMatrix b (wallLandingOp d)) (-z) * Complex.exp z := by
    filter_upwards [self_mem_nhdsWithin] with d hd
    rw [fredholmDetOp_smul_eq_detOneSub, detOneSub_eq b (hA d), opTrace_wallLandingOp hd]
    ring_nf
  have h0 : fredholmDetOp b (z • quantileWallOperator)
      = entireDet2 (coordMatrix b quantileWallOperator) (-z) * Complex.exp z := by
    rw [fredholmDetOp_smul_eq_detOneSub, detOneSub_eq b hA0, opTrace_quantileWallOperator]
    ring_nf
  rw [h0]
  exact (hdet.mul_const _).congr' (hev.mono fun d h => h.symm)

/-- `det(1 + z A_0)` is the exponential-wall Fredholm series. -/
theorem fredholmDetOp_quantileWallOperator {ι : Type*} [DecidableEq ι]
    (b : HilbertBasis ι ℂ (Lp ℂ 2 (volume.restrict (Ioo (0 : ℝ) 1)))) (z : ℂ) :
    fredholmDetOp b (z • quantileWallOperator)
      = routePPrimitiveGammaJuliaStokesWallFredholmEntireDet (expMeasure 1) z := by
  refine tendsto_nhds_unique (tendsto_fredholmDetOp_wallLandingOp b z) ?_
  refine (tendsto_routePPrimitiveGammaJuliaStokesWallFredholmEntireDet_nhdsGT_zero z).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with d hd
  exact (fredholmDetOp_wallLandingOp b hd z).symm

/-- **(SCIN.16).**  `det(1 + z U_d T(d) U_d*) → det(1 + z A_0)` locally uniformly in `z`. -/
theorem tendstoLocallyUniformly_fredholmDetOp_wallLandingOp {ι : Type*} [DecidableEq ι]
    (b : HilbertBasis ι ℂ (Lp ℂ 2 (volume.restrict (Ioo (0 : ℝ) 1)))) :
    TendstoLocallyUniformly (fun d (z : ℂ) => fredholmDetOp b (z • wallLandingOp d))
      (fun z : ℂ => fredholmDetOp b (z • quantileWallOperator)) (𝓝[>] 0) := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro C hC
  obtain ⟨ρ, hρ⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp hC.isBounded
  have hunif := (tendstoUniformlyOn_routePPrimitiveGammaJuliaStokesWallFredholmEntireDet_nhdsGT_zero
    (le_max_right ρ 0)).mono (hρ.trans (Metric.closedBall_subset_closedBall (le_max_left ρ 0)))
  refine (hunif.congr ?_).congr_right fun z _ => (fredholmDetOp_quantileWallOperator b z).symm
  filter_upwards [self_mem_nhdsWithin] with d hd z _
  exact (fredholmDetOp_wallLandingOp b hd z).symm

/-- **(SCIN.16), negative chamber.**  `det(1 + z U_d T(-d) U_d*) → det(1 - z A_0)` locally
uniformly in `z`. -/
theorem tendstoLocallyUniformly_fredholmDetOp_wallLandingOp_neg {ι : Type*} [DecidableEq ι]
    (b : HilbertBasis ι ℂ (Lp ℂ 2 (volume.restrict (Ioo (0 : ℝ) 1)))) :
    TendstoLocallyUniformly (fun d (z : ℂ) => fredholmDetOp b (z • -wallLandingOp d))
      (fun z : ℂ => fredholmDetOp b (z • -quantileWallOperator)) (𝓝[>] 0) := by
  have h := (tendstoLocallyUniformly_fredholmDetOp_wallLandingOp b).comp (fun z : ℂ => -z)
    continuous_neg
  simp only [Function.comp_def, neg_smul, smul_neg] at h ⊢
  exact h

/-- The landings converge in Hilbert–Schmidt and in operator norm. -/
theorem tendsto_hsNorm_wallLandingOp_sub :
    Tendsto (fun d => ContinuousLinearMap.hsNorm (wallLandingOp d - quantileWallOperator))
      (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun d => ‖wallLandingOp d - quantileWallOperator‖) (𝓝[>] 0) (𝓝 0) := by
  have hA0 := isHilbertSchmidt_quantileWallOperator
  have hA : ∀ d, IsHilbertSchmidt (wallLandingOp d) := fun d => by
    rw [wallLandingOp, quantileLandingOp_eq_adjoint_comp]
    exact (isHilbertSchmidt_quantileBurnolSynthesis _).comp_left _
  have hS := tendsto_hsNorm_wallSynthesis_sub.const_mul 2
  rw [mul_zero] at hS
  have hHS : Tendsto (fun d => ContinuousLinearMap.hsNorm (wallLandingOp d - quantileWallOperator))
      (𝓝[>] 0) (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hS
      (fun d => ContinuousLinearMap.hsNorm_nonneg _) hsNorm_wallLandingOp_sub_le
  exact ⟨hHS, tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hHS
    (fun d => norm_nonneg _) fun d => opNorm_le_hsNorm ((hA d).sub hA0)⟩

/-- **(SCIN.17).**  The comoving right and left limits `±A_0` carry the normalized prime Stokes
charge `½ (tr A_0 - tr(-A_0)) = 1 = (4 - (-4))/8`, and the pole–Gamma countercurrent carries
`((-4) - 4)/8 = -1`, so the completed scalar charge vanishes. -/
theorem comoving_charge_conservation :
    (1 / 2 : ℂ) * (opTrace quantileWallOperator - opTrace (-quantileWallOperator))
        = (((4 - (-4)) / 8 : ℝ) : ℂ) ∧
      Tendsto gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent (𝓝[>] 0) (𝓝 4) ∧
      Tendsto gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent (𝓝[<] 0) (𝓝 (-4)) ∧
      Tendsto gammaSewnMobiusApertureStokesOrientedPolarCountercurrent (𝓝[>] 0) (𝓝 (-4)) ∧
      Tendsto gammaSewnMobiusApertureStokesOrientedPolarCountercurrent (𝓝[<] 0) (𝓝 4) ∧
      (1 / 2 : ℂ) * (opTrace quantileWallOperator - opTrace (-quantileWallOperator))
        + ((((-4) - 4) / 8 : ℝ) : ℂ) = 0 := by
  obtain ⟨h1, h2, h3, h4, -, -⟩ := sourceStokes_charge_conservation
  refine ⟨?_, h1, h2, h3, h4, ?_⟩ <;> rw [half_opTrace_quantileWallOperator_sub_neg] <;> norm_num

/-- **The comoving landing theorem.**  For `d > 0` the comoving chart is an isometry carrying the
two chambers of the prime Stokes unit onto `±A_d`; `A_d → A_0` in trace norm; the determinants
`det(1 + z U_d T(±d) U_d*)` are the complete prime-tuple Fredholm series of the wall law and land
locally uniformly at `det(1 ± z A_0)`; and `½ (tr A_0 - tr(-A_0)) = 1`. -/
theorem sourceStokes_comoving_landing {ι : Type*} [DecidableEq ι]
    (b : HilbertBasis ι ℂ (Lp ℂ 2 (volume.restrict (Ioo (0 : ℝ) 1)))) :
    (∀ hd : 0 < d, adjoint (comovingChart hd) ∘L comovingChart hd = ContinuousLinearMap.id ℂ _ ∧
      comovingChart hd ∘L stokesCubicUnit d ∘L adjoint (comovingChart hd) = wallLandingOp d ∧
      comovingChart hd ∘L stokesCubicUnit (-d) ∘L adjoint (comovingChart hd) = -wallLandingOp d ∧
      ∀ z, fredholmDetOp b (z • (comovingChart hd ∘L stokesCubicUnit d ∘L
        adjoint (comovingChart hd))) = routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
          (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) z) ∧
    Tendsto (fun d => traceNorm (Lp ℂ 2 (volume.restrict (Ioo (0 : ℝ) 1)))
      (wallLandingOp d - quantileWallOperator)) (𝓝[>] 0) (𝓝 0) ∧
    TendstoLocallyUniformly (fun d (z : ℂ) => fredholmDetOp b (z • wallLandingOp d))
      (fun z : ℂ => fredholmDetOp b (z • quantileWallOperator)) (𝓝[>] 0) ∧
    TendstoLocallyUniformly (fun d (z : ℂ) => fredholmDetOp b (z • -wallLandingOp d))
      (fun z : ℂ => fredholmDetOp b (z • -quantileWallOperator)) (𝓝[>] 0) ∧
    (1 / 2 : ℂ) * (opTrace quantileWallOperator - opTrace (-quantileWallOperator)) = 1 :=
  ⟨fun hd => ⟨adjoint_comovingChart_comp hd, comovingChart_conj_stokesCubicUnit hd,
      comovingChart_conj_stokesCubicUnit_neg hd, fredholmDetOp_comovingChart_conj b hd⟩,
    tendsto_traceNorm_wallLandingOp_sub, tendstoLocallyUniformly_fredholmDetOp_wallLandingOp b,
    tendstoLocallyUniformly_fredholmDetOp_wallLandingOp_neg b,
    half_opTrace_quantileWallOperator_sub_neg⟩

end Determinant

end GaloisForLFunctions.HTGeometry
