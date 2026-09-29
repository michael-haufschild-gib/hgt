import GaloisForLFunctions.HTGeometry.HodgeCollisionRecord
import GaloisForLFunctions.HTGeometry.SourceStokesComovingLanding

/-!
# The literal prime-pair collision section

For aperture `d > 0` the atomic Stokes wall law `μ_d` has atoms `x_d(p) = 2d log p` of mass
`π_d(p)`, so the pair law `ν_d = μ_d ⊗ μ_d` has atoms `(x_d(p), x_d(q))` of mass `π_d(p)π_d(q)`.
The normalized atom indicators form a Hilbert basis of `L²(ν_d)`, giving a unitary chart
`J_d : ℓ²(Primes × Primes) → L²(ν_d)`.  Transporting the Cayley collision colligation of `ν_d`:

* the contrast `δ_{pq} = (log p - log q)/(log p + log q)` is the literal symbol of `S_d`, and
  `√(1 - λ_{pq})` that of `E_d`;
* `Z_d = ∑_{p,q} [λ_{pq}/(1 - λ_{pq})] A_d(p, q)²` with `A_d(p, q) = √(π_d(p)π_d(q)) κ(log p, log
q)`;
* `Ω_{H,d}(p, q) = Z_d^{-1/2} [δ_{pq}/√(1 - λ_{pq})] A_d(p, q)` and `e_{n,d} = E_d S_dⁿ Ω_{H,d}`;
* **Theorem CCRHD-D.**  `𝖳_d = ⊕ₙ |e_{n,d}⟩⟨e_{n,d}|` is positive, Schatten-one, with
  `tr 𝖳_d = ‖𝖳_d‖₁ = 1`, `‖𝖳_d‖ = ‖e_{0,d}‖² < 1`, and nonzero entries between arbitrary unequal
  prime-pair labels in every history grade.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory ContinuousLinearMap
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

local instance factTwoNeTopPrimePair : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩

/-- The prime-pair Hilbert space `ℓ²(Primes × Primes)`. -/
abbrev PrimePairHilbert := lp (fun _ : Nat.Primes × Nat.Primes => ℂ) 2

theorem inner_lpBasis_left {ι : Type*} [DecidableEq ι] (i : ι) (v : lp (fun _ : ι => ℂ) 2) :
    ⟪HilbertSchmidt.lpBasis ι i, v⟫_ℂ = v i := by
  rw [HilbertSchmidt.lpBasis_apply, lp.inner_single_left]
  simp

theorem norm_sq_lp_eq_tsum {ι : Type*} (v : lp (fun _ : ι => ℂ) 2) :
    ‖v‖ ^ 2 = ∑' i, ‖v i‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum two_toReal_pos v
  simpa [Real.rpow_two] using h

/-- The pair wall law `ν_d = μ_d ⊗ μ_d`. -/
abbrev pairWallLaw (d : ℝ) : Measure (ℝ × ℝ) :=
  (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d).prod
    (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d)

theorem ae_pos_wallHalfLineLaw (d : ℝ) :
    ∀ᵐ x ∂routePPrimitiveGammaJuliaStokesWallHalfLineLaw d, 0 < x := by
  by_cases hd : 0 < d
  · exact ae_wallHalfLineLaw_of_atoms hd measurableSet_Ioi fun p => wallLogCoordinate_pos hd p
  · rw [routePPrimitiveGammaJuliaStokesWallHalfLineLaw, if_neg hd]
    exact ae_pos_expMeasure_one

/-- `ν_d` is carried by the open quadrant for every `d`. -/
theorem ae_pos_pairWallLaw (d : ℝ) : ∀ᵐ z ∂pairWallLaw d, 0 < z.1 ∧ 0 < z.2 := by
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_pos_wallHalfLineLaw d),
    Measure.quasiMeasurePreserving_snd.ae (ae_pos_wallHalfLineLaw d)] with z h1 h2
  exact ⟨h1, h2⟩

theorem pairWallLaw_of_nonpos {d : ℝ} (hd : ¬0 < d) : pairWallLaw d = expPairLaw := by
  rw [pairWallLaw, routePPrimitiveGammaJuliaStokesWallHalfLineLaw, if_neg hd]

/-! ## Prime-pair atoms -/

section Atoms

variable {d : ℝ}

/-- The pair atom `(x_d(p), x_d(q))`. -/
def primePairAtom (d : ℝ) (pq : Nat.Primes × Nat.Primes) : ℝ × ℝ :=
  (routePPrimitiveGammaJuliaStokesWallLogCoordinate d pq.1,
    routePPrimitiveGammaJuliaStokesWallLogCoordinate d pq.2)

/-- The pair weight `π_d(p) π_d(q)`. -/
def pairWeight (d : ℝ) (pq : Nat.Primes × Nat.Primes) : ℝ :=
  stokesWeight d pq.1 * stokesWeight d pq.2

theorem pairWeight_pos (hd : 0 < d) (pq : Nat.Primes × Nat.Primes) : 0 < pairWeight d pq :=
  mul_pos (stokesWeight_pos hd _) (stokesWeight_pos hd _)

theorem pairWallLaw_atom (hd : 0 < d) (pq : Nat.Primes × Nat.Primes) :
    pairWallLaw d {primePairAtom d pq} = ENNReal.ofReal (pairWeight d pq) := by
  rw [primePairAtom, ← Set.singleton_prod_singleton, Measure.prod_prod, wallHalfLineLaw_atom hd,
    wallHalfLineLaw_atom hd, pairWeight, ENNReal.ofReal_mul (stokesWeight_pos hd _).le]

theorem pairWallLaw_real_atom (hd : 0 < d) (pq : Nat.Primes × Nat.Primes) :
    (pairWallLaw d).real {primePairAtom d pq} = pairWeight d pq := by
  rw [measureReal_def, pairWallLaw_atom hd, ENNReal.toReal_ofReal (pairWeight_pos hd pq).le]

theorem pairAtom_injective (hd : 0 < d) : Function.Injective (primePairAtom d) := by
  intro pq pq' h
  simp only [primePairAtom, Prod.mk.injEq] at h
  exact Prod.ext (wallLogCoordinate_injective hd h.1) (wallLogCoordinate_injective hd h.2)

/-- `ν_d` is carried by its atoms. -/
theorem ae_pairWallLaw_of_atoms (hd : 0 < d) {P : ℝ × ℝ → Prop}
    (h : ∀ pq, P (primePairAtom d pq)) : ∀ᵐ z ∂pairWallLaw d, P z := by
  have h1 : ∀ᵐ x ∂routePPrimitiveGammaJuliaStokesWallHalfLineLaw d,
      x ∈ Set.range (routePPrimitiveGammaJuliaStokesWallLogCoordinate d) :=
    ae_wallHalfLineLaw_of_atoms hd (Set.countable_range _).measurableSet fun p => ⟨p, rfl⟩
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae h1,
    Measure.quasiMeasurePreserving_snd.ae h1] with z hz1 hz2
  obtain ⟨p, hp⟩ := hz1
  obtain ⟨q, hq⟩ := hz2
  have hz : z = primePairAtom d (p, q) := Prod.ext hp.symm hq.symm
  rw [hz]
  exact h (p, q)

/-- Almost-everywhere equal functions agree at every pair atom. -/
theorem eq_at_pairAtom_of_ae_eq (hd : 0 < d) {f g : ℝ × ℝ → ℂ} (h : f =ᵐ[pairWallLaw d] g)
    (pq : Nat.Primes × Nat.Primes) : f (primePairAtom d pq) = g (primePairAtom d pq) := by
  by_contra hne
  have h0 := ae_iff.mp h
  have hle := (measure_mono (μ := pairWallLaw d)
    (Set.singleton_subset_iff.mpr (show primePairAtom d pq ∈ {a | ¬f a = g a} from hne))).trans
      (le_of_eq h0)
  rw [pairWallLaw_atom hd, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at hle
  exact absurd hle (not_le.mpr (pairWeight_pos hd pq))

/-- The normalized pair atom `(π_d(p)π_d(q))^{-1/2} 1_{(x_d(p), x_d(q))}`. -/
def pairAtomVector (d : ℝ) (pq : Nat.Primes × Nat.Primes) : Lp ℂ 2 (pairWallLaw d) :=
  (((Real.sqrt (pairWeight d pq))⁻¹ : ℝ) : ℂ) •
    indicatorConstLp 2 (measurableSet_singleton (primePairAtom d pq)) (measure_ne_top _ _) (1 : ℂ)

theorem pairAtomVector_ae (pq : Nat.Primes × Nat.Primes) :
    (pairAtomVector d pq : ℝ × ℝ → ℂ) =ᵐ[pairWallLaw d]
      fun z => (((Real.sqrt (pairWeight d pq))⁻¹ : ℝ) : ℂ) •
        ({primePairAtom d pq} : Set (ℝ × ℝ)).indicator (fun _ => (1 : ℂ)) z := by
  unfold pairAtomVector
  filter_upwards [Lp.coeFn_smul (((Real.sqrt (pairWeight d pq))⁻¹ : ℝ) : ℂ)
    (indicatorConstLp 2 (measurableSet_singleton (primePairAtom d pq))
      (measure_ne_top (pairWallLaw d) _) (1 : ℂ)),
    indicatorConstLp_coeFn (hs := measurableSet_singleton (primePairAtom d pq))
      (hμs := measure_ne_top (pairWallLaw d) _) (c := (1 : ℂ))] with z h1 h2
  rw [h1, Pi.smul_apply, h2]

theorem sqrt_pairWeight_ne_zero (hd : 0 < d) (pq : Nat.Primes × Nat.Primes) :
    ((Real.sqrt (pairWeight d pq) : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast (Real.sqrt_pos.mpr (pairWeight_pos hd pq)).ne'

theorem ofReal_pairWeight_eq (hd : 0 < d) (pq : Nat.Primes × Nat.Primes) :
    ((pairWeight d pq : ℝ) : ℂ)
      = ((Real.sqrt (pairWeight d pq) : ℝ) : ℂ) * ((Real.sqrt (pairWeight d pq) : ℝ) : ℂ) := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (pairWeight_pos hd pq).le]

/-- `⟪e_{pq}, f⟫ = √(π_d(p)π_d(q)) f(x_d(p), x_d(q))`. -/
theorem inner_pairAtomVector (hd : 0 < d) (pq : Nat.Primes × Nat.Primes)
    (f : Lp ℂ 2 (pairWallLaw d)) :
    ⟪pairAtomVector d pq, f⟫_ℂ
      = ((Real.sqrt (pairWeight d pq) : ℝ) : ℂ) * f (primePairAtom d pq) := by
  rw [pairAtomVector, inner_smul_left, L2.inner_indicatorConstLp_one, integral_singleton,
    pairWallLaw_real_atom hd, Complex.conj_ofReal, Complex.real_smul,
    ofReal_pairWeight_eq hd pq, Complex.ofReal_inv]
  field_simp [sqrt_pairWeight_ne_zero hd pq]

theorem inner_pairAtomVector_of_ae (hd : 0 < d) (pq : Nat.Primes × Nat.Primes)
    {f : Lp ℂ 2 (pairWallLaw d)} {F : ℝ × ℝ → ℂ} (h : (f : ℝ × ℝ → ℂ) =ᵐ[pairWallLaw d] F) :
    ⟪pairAtomVector d pq, f⟫_ℂ
      = ((Real.sqrt (pairWeight d pq) : ℝ) : ℂ) * F (primePairAtom d pq) := by
  rw [inner_pairAtomVector hd, eq_at_pairAtom_of_ae_eq hd h]

theorem pairAtomVector_apply_atom (hd : 0 < d) (pq pq' : Nat.Primes × Nat.Primes) :
    (pairAtomVector d pq' : ℝ × ℝ → ℂ) (primePairAtom d pq)
      = if pq = pq' then (((Real.sqrt (pairWeight d pq'))⁻¹ : ℝ) : ℂ) else 0 := by
  rw [eq_at_pairAtom_of_ae_eq hd (pairAtomVector_ae pq') pq]
  by_cases h : pq = pq'
  · subst h
    rw [Set.indicator_of_mem (Set.mem_singleton _), if_pos rfl, smul_eq_mul, mul_one]
  · rw [if_neg h, Set.indicator_of_notMem
      (fun hm => h (pairAtom_injective hd (Set.mem_singleton_iff.mp hm))), smul_zero]

theorem orthonormal_pairAtomVector (hd : 0 < d) : Orthonormal ℂ (pairAtomVector d) := by
  rw [orthonormal_iff_ite]
  intro pq pq'
  rw [inner_pairAtomVector hd, pairAtomVector_apply_atom hd]
  by_cases h : pq = pq'
  · subst h
    rw [if_pos rfl, if_pos rfl, Complex.ofReal_inv]
    exact mul_inv_cancel₀ (sqrt_pairWeight_ne_zero hd pq)
  · rw [if_neg h, if_neg h, mul_zero]

theorem orthogonal_span_pairAtomVector (hd : 0 < d) :
    (Submodule.span ℂ (Set.range (pairAtomVector d)))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro f hf
  have hzero : ∀ pq, (f : ℝ × ℝ → ℂ) (primePairAtom d pq) = 0 := by
    intro pq
    have h := (Submodule.mem_orthogonal _ f).mp hf (pairAtomVector d pq)
      (Submodule.subset_span ⟨pq, rfl⟩)
    rw [inner_pairAtomVector hd] at h
    exact (mul_eq_zero.mp h).resolve_left (sqrt_pairWeight_ne_zero hd pq)
  exact Lp.eq_zero_iff_ae_eq_zero.mpr (ae_pairWallLaw_of_atoms hd hzero)

/-- The pair-atom Hilbert basis of `L²(ν_d)`. -/
def pairAtomBasis (hd : 0 < d) :
    HilbertBasis (Nat.Primes × Nat.Primes) ℂ (Lp ℂ 2 (pairWallLaw d)) :=
  HilbertBasis.mkOfOrthogonalEqBot (orthonormal_pairAtomVector hd)
    (orthogonal_span_pairAtomVector hd)

theorem pairAtomBasis_apply (hd : 0 < d) (pq : Nat.Primes × Nat.Primes) :
    pairAtomBasis hd pq = pairAtomVector d pq := by
  rw [pairAtomBasis, HilbertBasis.coe_mkOfOrthogonalEqBot]

/-- The unitary pair chart `J_d : ℓ²(Primes × Primes) → L²(ν_d)`. -/
def pairAtomChart (hd : 0 < d) : PrimePairHilbert →L[ℂ] Lp ℂ 2 (pairWallLaw d) :=
  ((pairAtomBasis hd).repr.symm : PrimePairHilbert →L[ℂ] Lp ℂ 2 (pairWallLaw d))

theorem pairAtomChart_basis (hd : 0 < d) (pq : Nat.Primes × Nat.Primes) :
    pairAtomChart hd (HilbertSchmidt.lpBasis (Nat.Primes × Nat.Primes) pq)
      = pairAtomVector d pq := by
  rw [pairAtomChart, HilbertSchmidt.lpBasis_apply]
  change (pairAtomBasis hd).repr.symm (lp.single 2 pq 1) = _
  rw [HilbertBasis.repr_symm_single, pairAtomBasis_apply]

theorem pairAtomChart_comp_adjoint (hd : 0 < d) :
    pairAtomChart hd ∘L adjoint (pairAtomChart hd) = ContinuousLinearMap.id ℂ _ := by
  rw [pairAtomChart, LinearIsometryEquiv.adjoint_eq_symm, LinearIsometryEquiv.symm_symm]
  ext1 x
  exact (pairAtomBasis hd).repr.symm_apply_apply x

theorem adjoint_pairAtomChart_comp (hd : 0 < d) :
    adjoint (pairAtomChart hd) ∘L pairAtomChart hd = ContinuousLinearMap.id ℂ _ := by
  rw [pairAtomChart, LinearIsometryEquiv.adjoint_eq_symm, LinearIsometryEquiv.symm_symm]
  ext1 x
  exact (pairAtomBasis hd).repr.apply_symm_apply x

theorem norm_adjoint_pairAtomChart_apply (hd : 0 < d) (f : Lp ℂ 2 (pairWallLaw d)) :
    ‖adjoint (pairAtomChart hd) f‖ = ‖f‖ := by
  rw [pairAtomChart, LinearIsometryEquiv.adjoint_eq_symm, LinearIsometryEquiv.symm_symm]
  exact (pairAtomBasis hd).repr.norm_map f

/-- The coordinates of `J_d* f` are the atom values `√(π_d(p)π_d(q)) f(x_d(p), x_d(q))`. -/
theorem adjoint_pairAtomChart_apply_of_ae (hd : 0 < d) {f : Lp ℂ 2 (pairWallLaw d)}
    {F : ℝ × ℝ → ℂ} (h : (f : ℝ × ℝ → ℂ) =ᵐ[pairWallLaw d] F) (pq : Nat.Primes × Nat.Primes) :
    adjoint (pairAtomChart hd) f pq
      = ((Real.sqrt (pairWeight d pq) : ℝ) : ℂ) * F (primePairAtom d pq) := by
  rw [← inner_lpBasis_left, adjoint_inner_right, pairAtomChart_basis,
    inner_pairAtomVector_of_ae hd pq h]

end Atoms

/-! ## The literal prime-pair colligation -/

section Literal

variable {d : ℝ}

theorem collisionSurvival_coeFn {ν : Measure (ℝ × ℝ)} (f : Lp ℂ 2 ν) :
    (collisionSurvival ν f : ℝ × ℝ → ℂ) =ᵐ[ν] fun z => (pairContrast z : ℂ) * (f : ℝ × ℝ → ℂ) z :=
  contractionMul_coeFn ν _ _ f

theorem collisionExit_coeFn {ν : Measure (ℝ × ℝ)} (f : Lp ℂ 2 ν) :
    (collisionExit ν f : ℝ × ℝ → ℂ) =ᵐ[ν] fun z => (pairCoherence z : ℂ) * (f : ℝ × ℝ → ℂ) z :=
  contractionMul_coeFn ν _ _ f

theorem primes_log_pos (p : Nat.Primes) : 0 < Real.log (p : ℝ) :=
  Real.log_pos (by exact_mod_cast p.prop.one_lt)

/-- The prime-pair Cayley contrast `δ_{pq} = (log p - log q)/(log p + log q)`. -/
def primePairContrast (pq : Nat.Primes × Nat.Primes) : ℝ :=
  cayleyContrast (Real.log (pq.1 : ℝ)) (Real.log (pq.2 : ℝ))

theorem primePairContrast_mem_Ioo (pq : Nat.Primes × Nat.Primes) :
    primePairContrast pq ∈ Ioo (-1 : ℝ) 1 :=
  cayleyContrast_mem_Ioo (primes_log_pos pq.1) (primes_log_pos pq.2)

theorem one_sub_primePairContrast_sq_pos (pq : Nat.Primes × Nat.Primes) :
    0 < 1 - primePairContrast pq ^ 2 := by
  have h := primePairContrast_mem_Ioo pq
  nlinarith [h.1, h.2]

theorem primePairContrast_ne_zero {pq : Nat.Primes × Nat.Primes} (h : pq.1 ≠ pq.2) :
    primePairContrast pq ≠ 0 := by
  have hp := primes_log_pos pq.1
  have hq := primes_log_pos pq.2
  rw [primePairContrast, cayleyContrast]
  refine div_ne_zero (fun hs => h ?_) (by linarith)
  have hlog : Real.log (pq.1 : ℝ) = Real.log (pq.2 : ℝ) := by linarith
  have hp' : (0 : ℝ) < (pq.1 : ℕ) := by exact_mod_cast pq.1.prop.pos
  have hq' : (0 : ℝ) < (pq.2 : ℕ) := by exact_mod_cast pq.2.prop.pos
  have := Real.log_injOn_pos (Set.mem_Ioi.mpr hp') (Set.mem_Ioi.mpr hq') hlog
  exact Subtype.ext (by exact_mod_cast this)

/-- The contrast is scale-free: `δ(x_d(p), x_d(q)) = δ_{pq}`. -/
theorem pairContrast_pairAtom (hd : 0 < d) (pq : Nat.Primes × Nat.Primes) :
    pairContrast (primePairAtom d pq) = primePairContrast pq := by
  have hp := primes_log_pos pq.1
  have hq := primes_log_pos pq.2
  rw [primePairAtom, pairContrast_of_pos (wallLogCoordinate_pos hd pq.1)
    (wallLogCoordinate_pos hd pq.2), primePairContrast, cayleyContrast, cayleyContrast,
    routePPrimitiveGammaJuliaStokesWallLogCoordinate,
    routePPrimitiveGammaJuliaStokesWallLogCoordinate]
  have h1 : Real.log (pq.1 : ℝ) + Real.log (pq.2 : ℝ) ≠ 0 := by linarith
  have h2 : 2 * d ≠ 0 := by positivity
  rw [← mul_sub, ← mul_add, mul_div_mul_left _ _ h2]

/-- The literal amplitude `A_d(p, q) = √(π_d(p)π_d(q)) κ(log p, log q)`. -/
def primePairAmplitude (d : ℝ) (pq : Nat.Primes × Nat.Primes) : ℝ :=
  Real.sqrt (pairWeight d pq) * wallCubicKernel (Real.log (pq.1 : ℝ)) (Real.log (pq.2 : ℝ))

theorem wallCubicKernel_primePair (pq : Nat.Primes × Nat.Primes) :
    wallCubicKernel (Real.log (pq.1 : ℝ)) (Real.log (pq.2 : ℝ))
      = Real.sqrt (1 - primePairContrast pq ^ 2) ^ 3 :=
  (cayley_pair_identities (primes_log_pos pq.1) (primes_log_pos pq.2)).2.2

/-- **(CCRHD.18).**  `Z_d = ∑_{p,q} [λ_{pq}/(1 - λ_{pq})] A_d(p, q)²`. -/
def primePairMass (d : ℝ) : ℝ :=
  ∑' pq, primePairContrast pq ^ 2 / (1 - primePairContrast pq ^ 2) * primePairAmplitude d pq ^ 2

theorem primePairMass_term (hd : 0 < d) (pq : Nat.Primes × Nat.Primes) :
    primePairContrast pq ^ 2 / (1 - primePairContrast pq ^ 2) * primePairAmplitude d pq ^ 2
      = pairWeight d pq * collisionProfile (primePairAtom d pq) ^ 2 := by
  have hpos := one_sub_primePairContrast_sq_pos pq
  rw [primePairAmplitude, wallCubicKernel_primePair, mul_pow,
    Real.sq_sqrt (pairWeight_pos hd pq).le,
    ← pow_mul, show 3 * 2 = 2 * 3 by norm_num, pow_mul, Real.sq_sqrt hpos.le, collisionProfile,
    pairContrast_pairAtom hd]
  field_simp

/-- **(CCRHD.18).**  The collision normalizer of `ν_d` is the literal prime-pair sum `Z_d`. -/
theorem collisionMass_pairWallLaw (hd : 0 < d) :
    collisionMass (pairWallLaw d) = primePairMass d := by
  have hmem : MemLp (fun z => (collisionProfile z : ℂ)) 2 (pairWallLaw d) :=
    MemLp.of_bound (Complex.measurable_ofReal.comp measurable_collisionProfile).aestronglyMeasurable
      1 (Eventually.of_forall fun z => by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact abs_collisionProfile_le_one z)
  have h1 : collisionMass (pairWallLaw d) = ‖hmem.toLp _‖ ^ 2 := by
    rw [norm_sq_L2_toLp, collisionMass]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [h1, ← norm_adjoint_pairAtomChart_apply hd, norm_sq_lp_eq_tsum, primePairMass]
  refine tsum_congr fun pq => ?_
  rw [adjoint_pairAtomChart_apply_of_ae hd hmem.coeFn_toLp, norm_mul, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, sq_abs, sq_abs,
    Real.sq_sqrt (pairWeight_pos hd pq).le, primePairMass_term hd pq]

/-- The two smallest primes. -/
def primePairTwoThree : Nat.Primes × Nat.Primes := (⟨2, Nat.prime_two⟩, ⟨3, Nat.prime_three⟩)

theorem primePairTwoThree_ne : primePairTwoThree.1 ≠ primePairTwoThree.2 := by
  intro h
  have := congrArg Subtype.val h
  simp [primePairTwoThree] at this

/-- `Z_d > 0` for every aperture. -/
theorem collisionMass_pairWallLaw_pos (d : ℝ) : 0 < collisionMass (pairWallLaw d) := by
  by_cases hd : 0 < d
  · have hint : Integrable (fun z => collisionProfile z ^ 2) (pairWallLaw d) :=
      integrable_of_abs_le (pairWallLaw d) (measurable_collisionProfile.pow_const 2) (C := 1)
        fun z => by
          rw [abs_of_nonneg (sq_nonneg _)]
          nlinarith [abs_collisionProfile_le_one z, sq_abs (collisionProfile z),
            abs_nonneg (collisionProfile z)]
    rw [collisionMass, integral_pos_iff_support_of_nonneg (fun z => sq_nonneg _) hint]
    have hmem : primePairAtom d primePairTwoThree ∈
        Function.support fun z => collisionProfile z ^ 2 := by
      rw [Function.mem_support, collisionProfile, pairContrast_pairAtom hd]
      exact pow_ne_zero 2 (mul_ne_zero (primePairContrast_ne_zero primePairTwoThree_ne)
        (one_sub_primePairContrast_sq_pos _).ne')
    refine lt_of_lt_of_le ?_ (measure_mono (Set.singleton_subset_iff.mpr hmem))
    rw [pairWallLaw_atom hd]
    exact ENNReal.ofReal_pos.mpr (pairWeight_pos hd _)
  · rw [pairWallLaw_of_nonpos hd]
    exact collisionMass_expPair_pos

theorem primePairMass_pos (hd : 0 < d) : 0 < primePairMass d := by
  rw [← collisionMass_pairWallLaw hd]
  exact collisionMass_pairWallLaw_pos d

/-- **(CCRHD.19).**  The literal Hodge state `Ω_{H,d} = J_d* Ω_{ν_d}` on `ℓ²(Primes × Primes)`. -/
def primePairState (hd : 0 < d) : PrimePairHilbert :=
  adjoint (pairAtomChart hd) (collisionState (pairWallLaw d))

/-- **(CCRHD.19).**  `Ω_{H,d}(p, q) = Z_d^{-1/2} [δ_{pq}/√(1 - λ_{pq})] A_d(p, q)`. -/
theorem primePairState_apply (hd : 0 < d) (pq : Nat.Primes × Nat.Primes) :
    primePairState hd pq = (((Real.sqrt (primePairMass d))⁻¹ *
      (primePairContrast pq / Real.sqrt (1 - primePairContrast pq ^ 2)) *
        primePairAmplitude d pq : ℝ) : ℂ) := by
  have hpos := one_sub_primePairContrast_sq_pos pq
  have hs : 0 < Real.sqrt (1 - primePairContrast pq ^ 2) := Real.sqrt_pos.mpr hpos
  have hsq := Real.sq_sqrt hpos.le
  rw [primePairState, adjoint_pairAtomChart_apply_of_ae hd (collisionState_coeFn _),
    collisionAmplitude, collisionMass_pairWallLaw hd, collisionProfile, pairContrast_pairAtom hd,
    primePairAmplitude, wallCubicKernel_primePair, ← Complex.ofReal_mul]
  congr 1
  have key : primePairContrast pq / Real.sqrt (1 - primePairContrast pq ^ 2) *
      Real.sqrt (1 - primePairContrast pq ^ 2) ^ 3
      = primePairContrast pq * Real.sqrt (1 - primePairContrast pq ^ 2) ^ 2 := by
    rw [div_mul_eq_mul_div, div_eq_iff hs.ne']
    ring
  calc Real.sqrt (pairWeight d pq) * ((Real.sqrt (primePairMass d))⁻¹ *
        (primePairContrast pq * (1 - primePairContrast pq ^ 2)))
      = (Real.sqrt (primePairMass d))⁻¹ * Real.sqrt (pairWeight d pq) *
          (primePairContrast pq * Real.sqrt (1 - primePairContrast pq ^ 2) ^ 2) := by
        rw [hsq]; ring
    _ = _ := by rw [← key]; ring

/-- The literal survival operator `S_d = J_d* S J_d`. -/
def primePairSurvival (hd : 0 < d) : PrimePairHilbert →L[ℂ] PrimePairHilbert :=
  adjoint (pairAtomChart hd) ∘L collisionSurvival (pairWallLaw d) ∘L pairAtomChart hd

/-- The literal exit operator `E_d = J_d* E₀ J_d`. -/
def primePairExit (hd : 0 < d) : PrimePairHilbert →L[ℂ] PrimePairHilbert :=
  adjoint (pairAtomChart hd) ∘L collisionExit (pairWallLaw d) ∘L pairAtomChart hd

/-- **(CCRHD.19).**  `S_d` is the diagonal operator `δ_{pq}`. -/
theorem inner_primePairSurvival (hd : 0 < d) (pq pq' : Nat.Primes × Nat.Primes) :
    ⟪HilbertSchmidt.lpBasis _ pq, primePairSurvival hd (HilbertSchmidt.lpBasis _ pq')⟫_ℂ
      = if pq = pq' then (primePairContrast pq : ℂ) else 0 := by
  rw [primePairSurvival, comp_apply, comp_apply, adjoint_inner_right, pairAtomChart_basis,
    pairAtomChart_basis, inner_pairAtomVector_of_ae hd pq (collisionSurvival_coeFn _),
    pairAtomVector_apply_atom hd, pairContrast_pairAtom hd]
  split_ifs with h
  · subst h
    rw [Complex.ofReal_inv]
    field_simp [sqrt_pairWeight_ne_zero hd pq]
  · rw [mul_zero, mul_zero]

/-- **(CCRHD.19).**  `E_d` is the diagonal operator `√(1 - λ_{pq})`. -/
theorem inner_primePairExit (hd : 0 < d) (pq pq' : Nat.Primes × Nat.Primes) :
    ⟪HilbertSchmidt.lpBasis _ pq, primePairExit hd (HilbertSchmidt.lpBasis _ pq')⟫_ℂ
      = if pq = pq' then ((Real.sqrt (1 - primePairContrast pq ^ 2) : ℝ) : ℂ) else 0 := by
  rw [primePairExit, comp_apply, comp_apply, adjoint_inner_right, pairAtomChart_basis,
    pairAtomChart_basis, inner_pairAtomVector_of_ae hd pq (collisionExit_coeFn _),
    pairAtomVector_apply_atom hd, pairCoherence, pairContrast_pairAtom hd]
  split_ifs with h
  · subst h
    rw [Complex.ofReal_inv]
    field_simp [sqrt_pairWeight_ne_zero hd pq]
  · rw [mul_zero, mul_zero]

theorem pairAtomChart_adjoint_apply (hd : 0 < d) (f : Lp ℂ 2 (pairWallLaw d)) :
    pairAtomChart hd (adjoint (pairAtomChart hd) f) = f := by
  have := congrArg (fun A : Lp ℂ 2 (pairWallLaw d) →L[ℂ] Lp ℂ 2 (pairWallLaw d) => A f)
    (pairAtomChart_comp_adjoint hd)
  simpa using this

theorem primePairSurvival_pow_apply (hd : 0 < d) (n : ℕ) (a : PrimePairHilbert) :
    (primePairSurvival hd ^ n) a
      = adjoint (pairAtomChart hd)
          ((collisionSurvival (pairWallLaw d) ^ n) (pairAtomChart hd a)) := by
  induction n generalizing a with
  | zero =>
    have := congrArg (fun A : PrimePairHilbert →L[ℂ] PrimePairHilbert => A a)
      (adjoint_pairAtomChart_comp hd)
    simpa [one_def] using this.symm
  | succ n ih =>
    rw [pow_succ, mul_def, comp_apply, ih, primePairSurvival, comp_apply, comp_apply,
      pairAtomChart_adjoint_apply, pow_succ, mul_def, comp_apply]

/-- The literal exit vectors `e_{n,d} = J_d* e_n(ν_d)`. -/
def primePairExitVector (hd : 0 < d) (n : ℕ) : PrimePairHilbert :=
  adjoint (pairAtomChart hd) (collisionExitVector (pairWallLaw d) n)

/-- **(CCRHD.19).**  `e_{n,d} = E_d S_dⁿ Ω_{H,d}`. -/
theorem primePairExitVector_eq (hd : 0 < d) (n : ℕ) :
    primePairExitVector hd n
      = primePairExit hd ((primePairSurvival hd ^ n) (primePairState hd)) := by
  rw [primePairSurvival_pow_apply, primePairState, pairAtomChart_adjoint_apply, primePairExit,
    comp_apply, comp_apply, pairAtomChart_adjoint_apply]
  rfl

/-- `e_{n,d}(p, q) = √(1 - λ_{pq}) δ_{pq}ⁿ Ω_{H,d}(p, q)`. -/
theorem primePairExitVector_apply (hd : 0 < d) (n : ℕ) (pq : Nat.Primes × Nat.Primes) :
    primePairExitVector hd n pq
      = ((Real.sqrt (1 - primePairContrast pq ^ 2) * primePairContrast pq ^ n : ℝ) : ℂ) *
          primePairState hd pq := by
  rw [primePairExitVector, adjoint_pairAtomChart_apply_of_ae hd (collisionExitVector_coeFn _ n),
    primePairState, adjoint_pairAtomChart_apply_of_ae hd (collisionState_coeFn _), pairCoherence,
    pairContrast_pairAtom hd]
  push_cast
  ring

theorem norm_primePairExitVector (hd : 0 < d) (n : ℕ) :
    ‖primePairExitVector hd n‖ = ‖collisionExitVector (pairWallLaw d) n‖ :=
  norm_adjoint_pairAtomChart_apply hd _

theorem summable_norm_primePairExitVector_sq (hd : 0 < d) :
    Summable fun n => ‖primePairExitVector hd n‖ ^ 2 :=
  (summable_norm_collisionExitVector_sq (pairWallLaw d) (ae_pos_pairWallLaw d)).congr fun n => by
    rw [norm_primePairExitVector]

/-- **(CCRHD.19).**  The literal prime-pair record `𝖳_d = ⊕ₙ |e_{n,d}⟩⟨e_{n,d}|`. -/
def primePairRecord (hd : 0 < d) : HistoryL2 PrimePairHilbert →L[ℂ] HistoryL2 PrimePairHilbert :=
  recordOp (primePairExitVector hd) (summable_norm_primePairExitVector_sq hd)

/-- **Theorem CCRHD-D.**  `𝖳_d ≥ 0`, `𝖳_d ∈ S₁`, `tr 𝖳_d = ‖𝖳_d‖₁ = 1`, `‖𝖳_d‖ = ‖e_{0,d}‖² < 1`,
and `tr((Q_N ⊗ 1) 𝖳_d) = ‖S_dᴺ Ω_{H,d}‖²`. -/
theorem primePairRecord_nuclear (hd : 0 < d) :
    (primePairRecord hd).IsPositive ∧ MemSchattenClass 1 (primePairRecord hd) ∧
      opTrace (primePairRecord hd) = 1 ∧
      traceNorm (HistoryL2 PrimePairHilbert) (primePairRecord hd) = 1 ∧
      ‖primePairRecord hd‖ = ‖primePairExitVector hd 0‖ ^ 2 ∧
      ‖primePairRecord hd‖ < 1 ∧
      ∀ N, opTrace (historyTailProjection N ∘L primePairRecord hd)
        = ((‖(primePairSurvival hd ^ N) (primePairState hd)‖ ^ 2 : ℝ) : ℂ) := by
  have hν := ae_pos_pairWallLaw d
  have hZ := collisionMass_pairWallLaw_pos d
  have htsum : ∑' n, ‖primePairExitVector hd n‖ ^ 2 = 1 := by
    simp_rw [norm_primePairExitVector]
    exact tsum_norm_collisionExitVector_sq hν hZ
  obtain ⟨hpos, hS1, htr⟩ := recordOp_traceClass (primePairExitVector hd)
    (summable_norm_primePairExitVector_sq hd)
  have hnorm : ‖primePairRecord hd‖ = ‖primePairExitVector hd 0‖ ^ 2 :=
    norm_recordOp _ _ fun n => by
      rw [norm_primePairExitVector, norm_primePairExitVector]
      exact norm_collisionExitVector_le _ n
  refine ⟨hpos, hS1, ?_, ?_, hnorm, ?_, fun N => ?_⟩
  · rw [primePairRecord, htr, htsum, Complex.ofReal_one]
  · rw [primePairRecord, traceNorm_recordOp, htsum]
  · rw [hnorm, norm_primePairExitVector, ← norm_collisionRecord hν]
    exact norm_collisionRecord_lt_one hν hZ
  · rw [primePairRecord, opTrace_historyTail_recordOp]
    have h := (hasSum_norm_exit_sq_tail (collision_colligation (pairWallLaw d))
      (collision_stable (pairWallLaw d) hν) (collisionState (pairWallLaw d)) N).tsum_eq
    rw [primePairSurvival_pow_apply, primePairState, pairAtomChart_adjoint_apply,
      norm_adjoint_pairAtomChart_apply]
    simp_rw [norm_primePairExitVector]
    exact congrArg (fun r : ℝ => (r : ℂ)) h

/-- **Theorem CCRHD-D, matrix.**  The entries `1_{n=k} e_{n,d}(p, q) conj(e_{n,d}(p', q'))`. -/
theorem inner_primePairRecord (hd : 0 < d) (n k : ℕ) (pq pq' : Nat.Primes × Nat.Primes) :
    ⟪(lp.single 2 n (HilbertSchmidt.lpBasis _ pq) : HistoryL2 PrimePairHilbert),
      primePairRecord hd (lp.single 2 k (HilbertSchmidt.lpBasis _ pq'))⟫_ℂ
      = if n = k then primePairExitVector hd n pq * conj (primePairExitVector hd n pq') else 0 := by
  rw [primePairRecord, inner_single_recordOp_single]
  split_ifs
  · rw [inner_lpBasis_left, ← inner_conj_symm, inner_lpBasis_left, mul_comm]
  · rfl

theorem primePairState_ne_zero (hd : 0 < d) {pq : Nat.Primes × Nat.Primes} (h : pq.1 ≠ pq.2) :
    primePairState hd pq ≠ 0 := by
  have hpos := one_sub_primePairContrast_sq_pos pq
  rw [primePairState_apply, Complex.ofReal_ne_zero, primePairAmplitude, wallCubicKernel_primePair]
  have h1 := inv_pos.mpr (Real.sqrt_pos.mpr (primePairMass_pos hd))
  have h2 := Real.sqrt_pos.mpr hpos
  have h3 := Real.sqrt_pos.mpr (pairWeight_pos hd pq)
  have h4 := primePairContrast_ne_zero h
  positivity

/-- **Theorem CCRHD-D.**  Every positive grade has nonzero entries between arbitrary unequal
prime-pair labels. -/
theorem inner_primePairRecord_ne_zero (hd : 0 < d) (n : ℕ) {pq pq' : Nat.Primes × Nat.Primes}
    (h : pq.1 ≠ pq.2) (h' : pq'.1 ≠ pq'.2) :
    ⟪(lp.single 2 n (HilbertSchmidt.lpBasis _ pq) : HistoryL2 PrimePairHilbert),
      primePairRecord hd (lp.single 2 n (HilbertSchmidt.lpBasis _ pq'))⟫_ℂ ≠ 0 := by
  rw [inner_primePairRecord, if_pos rfl, primePairExitVector_apply, primePairExitVector_apply]
  have hne : ∀ {r : Nat.Primes × Nat.Primes}, r.1 ≠ r.2 →
      ((Real.sqrt (1 - primePairContrast r ^ 2) * primePairContrast r ^ n : ℝ) : ℂ) ≠ 0 := by
    intro r hr
    rw [Complex.ofReal_ne_zero]
    exact mul_ne_zero (Real.sqrt_pos.mpr (one_sub_primePairContrast_sq_pos r)).ne'
      (pow_ne_zero n (primePairContrast_ne_zero hr))
  refine mul_ne_zero (mul_ne_zero (hne h) (primePairState_ne_zero hd h)) ?_
  rw [map_ne_zero]
  exact mul_ne_zero (hne h') (primePairState_ne_zero hd h')

end Literal

end GaloisForLFunctions.HTGeometry
