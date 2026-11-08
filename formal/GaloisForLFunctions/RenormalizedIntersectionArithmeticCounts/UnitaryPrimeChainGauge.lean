import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.CompletedPrimeBoundary
import GaloisForLFunctions.HTGeometry.WeightedAtomHilbert
import GaloisForLFunctions.EffectiveScalingGeometry.PrimeChainBasis

/-!
# Unitary vertical transport of completed prime exterior chains

The canonical prime-face basis embeds the actual finite exterior chains densely
and faithfully in the prescribed conductor-weighted Hilbert space. Imaginary
Dirichlet gauges extend to explicit unitaries in every exterior degree and
transport the original finite boundary graphs and their closures. This comparison
requires no boundedness or closability premise for the differentials.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open RHTower EffectiveScalingGeometry

attribute [local instance] primeLabelLinearOrder

abbrev PrimeFaceIndex (k : ℕ) := Set.powersetCard Nat.Primes k
abbrev PrimeExteriorHilbert (k : ℕ) := lp (fun _ : PrimeFaceIndex k=>ℂ) 2

/-- The Dirichlet multiplier attached to an increasing prime face. -/
def primeFaceMultiplier (z : ℂ) {k : ℕ} (S : PrimeFaceIndex k) : ℂ :=
  ∏ i : Fin k, ((Set.powersetCard.ofFinEmbEquiv.symm S i : Nat.Primes):ℂ)^z

/-- The algebraic gauge acts diagonally on the actual canonical exterior basis. -/
theorem dirichletChainGauge_basis (z : ℂ) (k : ℕ) (S : PrimeFaceIndex k) :
    dirichletChainGauge z k (primeChainBasis ℂ k S)=
      primeFaceMultiplier z S • primeChainBasis ℂ k S := by
  rw [primeChainBasis_eq_atom,dirichletChainGauge_atom]
  rfl

/-- Imaginary Dirichlet shifts give unit-modulus multipliers on every prime face. -/
theorem primeFaceMultiplier_imag_norm (t : ℝ) {k : ℕ} (S : PrimeFaceIndex k) :
    ‖primeFaceMultiplier ((t:ℂ)*Complex.I) S‖=1 := by
  rw [primeFaceMultiplier,norm_prod]
  apply prod_eq_one
  intro i _
  rw [Complex.norm_natCast_cpow_of_pos
    (Set.powersetCard.ofFinEmbEquiv.symm S i).property.pos]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.I_re,mul_zero,
    Complex.ofReal_im,Complex.I_im,zero_mul,sub_self,Real.rpow_zero]

/-- The Hilbert realization of the canonical exterior basis. -/
def primeExteriorEmbedding0 (k : ℕ) : PrimeChainSpace ℂ k →ₗ[ℂ] PrimeExteriorHilbert k :=
  (Finsupp.linearCombination ℂ (HilbertSchmidt.lpBasis (PrimeFaceIndex k))).comp
    (primeChainBasis ℂ k).repr.toLinearMap

theorem primeExteriorEmbedding0_basis (k : ℕ) (S : PrimeFaceIndex k) :
    primeExteriorEmbedding0 k (primeChainBasis ℂ k S)=HilbertSchmidt.lpBasis (PrimeFaceIndex k) S := by
  simp only [primeExteriorEmbedding0,LinearMap.comp_apply,LinearEquiv.coe_coe,
    Module.Basis.repr_self,Finsupp.linearCombination_single,one_smul]

/-- Normalize the prescribed conductor weight through the actual finite-chain gauge. -/
def primeExteriorEmbedding (δ : ℝ) (k : ℕ) :
    PrimeChainSpace ℂ k →ₗ[ℂ] PrimeExteriorHilbert k :=
  (primeExteriorEmbedding0 k).comp (dirichletChainGauge ((δ/2:ℝ):ℂ) k)

/-- The squared norm of a face multiplier is exactly its conductor weight. -/
theorem primeFaceMultiplier_real_norm_sq (δ : ℝ) {k : ℕ} (S : PrimeFaceIndex k) :
    ‖primeFaceMultiplier ((δ/2:ℝ):ℂ) S‖^2=
      ∏ i : Fin k, ((Set.powersetCard.ofFinEmbEquiv.symm S i : Nat.Primes):ℝ)^δ := by
  rw [primeFaceMultiplier,norm_prod,←Finset.prod_pow]
  apply prod_congr rfl
  intro i _
  have hp : (0:ℝ)<(Set.powersetCard.ofFinEmbEquiv.symm S i : Nat.Primes) := by
    exact_mod_cast (Set.powersetCard.ofFinEmbEquiv.symm S i).property.pos
  rw [Complex.norm_natCast_cpow_of_pos
    (Set.powersetCard.ofFinEmbEquiv.symm S i).property.pos,Complex.ofReal_re,pow_two,
    ←Real.rpow_add hp]
  congr 1
  ring

/-- The completed norm retains precisely the original weighted finite face coefficients. -/
theorem primeExteriorEmbedding_norm_sq (δ : ℝ) (k : ℕ) (a : PrimeChainSpace ℂ k) :
    ‖primeExteriorEmbedding δ k a‖^2=
      ∑ S∈((primeChainBasis ℂ k).repr a).support,
        (∏ i : Fin k, ((Set.powersetCard.ofFinEmbEquiv.symm S i : Nat.Primes):ℝ)^δ)*
          ‖(primeChainBasis ℂ k).repr a S‖^2 := by
  have he : primeExteriorEmbedding δ k=
      (Finsupp.linearCombination ℂ (fun S : PrimeFaceIndex k=>
        primeFaceMultiplier ((δ/2:ℝ):ℂ) S • HilbertSchmidt.lpBasis (PrimeFaceIndex k) S)).comp
          (primeChainBasis ℂ k).repr.toLinearMap := by
    apply (primeChainBasis ℂ k).ext
    intro S
    simp only [primeExteriorEmbedding,LinearMap.comp_apply,dirichletChainGauge_basis,
      map_smul,primeExteriorEmbedding0_basis,LinearEquiv.coe_coe,Module.Basis.repr_self,
      Finsupp.linearCombination_single,one_smul]
  rw [he,LinearMap.comp_apply,Finsupp.linearCombination_apply]
  change ‖∑ S∈((primeChainBasis ℂ k).repr a).support,
    (primeChainBasis ℂ k).repr a S •
      (primeFaceMultiplier ((δ/2:ℝ):ℂ) S • HilbertSchmidt.lpBasis (PrimeFaceIndex k) S)‖^2=_
  simp only [smul_smul]
  rw [HTGeometry.norm_sq_sum_smul_orthonormal
    (HilbertSchmidt.lpBasis (PrimeFaceIndex k)).orthonormal]
  apply sum_congr rfl
  intro S _
  rw [norm_mul,mul_pow,primeFaceMultiplier_real_norm_sq,mul_comm]

/-- The full-degree phase gauge is a constructed unitary on the completed carrier. -/
def primeExteriorUnitary (t : ℝ) (k : ℕ) :
    PrimeExteriorHilbert k ≃ₗᵢ[ℂ] PrimeExteriorHilbert k :=
  HTGeometry.lpPhaseUnitary (primeFaceMultiplier ((t:ℂ)*Complex.I))
    (primeFaceMultiplier_imag_norm t)

theorem primeExteriorUnitary_basis (t : ℝ) (k : ℕ) (S : PrimeFaceIndex k) :
    primeExteriorUnitary t k (HilbertSchmidt.lpBasis (PrimeFaceIndex k) S)=
      primeFaceMultiplier ((t:ℂ)*Complex.I) S • HilbertSchmidt.lpBasis (PrimeFaceIndex k) S := by
  apply lp.ext
  funext T
  simp only [primeExteriorUnitary,HTGeometry.lpPhaseUnitary_apply,
    HilbertSchmidt.lpBasis_apply,lp.single_apply,Pi.single_apply,lp.coeFn_smul,
    Pi.smul_apply,smul_eq_mul]
  by_cases h : T=S
  · subst T
    simp only [ite_true]
  · simp only [if_neg h,mul_zero]

/-- The constructed unitary extends the original finite exterior gauge exactly. -/
theorem primeExteriorUnitary_finite0 (t : ℝ) (k : ℕ) :
    (primeExteriorUnitary t k).toLinearEquiv.toLinearMap.comp (primeExteriorEmbedding0 k)=
      (primeExteriorEmbedding0 k).comp (dirichletChainGauge ((t:ℂ)*Complex.I) k) := by
  apply (primeChainBasis ℂ k).ext
  intro S
  change primeExteriorUnitary t k (primeExteriorEmbedding0 k (primeChainBasis ℂ k S)) = _
  rw [primeExteriorEmbedding0_basis,primeExteriorUnitary_basis,LinearMap.comp_apply,dirichletChainGauge_basis,map_smul,
    primeExteriorEmbedding0_basis]

/-- Every conductor weight retains the same finite imaginary gauge comparison. -/
theorem primeExteriorUnitary_finite (δ t : ℝ) (k : ℕ) :
    (primeExteriorUnitary t k).toLinearEquiv.toLinearMap.comp (primeExteriorEmbedding δ k)=
      (primeExteriorEmbedding δ k).comp (dirichletChainGauge ((t:ℂ)*Complex.I) k) := by
  rw [primeExteriorEmbedding,←LinearMap.comp_assoc,primeExteriorUnitary_finite0,
    LinearMap.comp_assoc,dirichletChainGauge_add]
  rw [LinearMap.comp_assoc,dirichletChainGauge_add,add_comm]

/-- The normalization preserves every algebraic chain faithfully. -/
theorem primeExteriorEmbedding_injective (δ : ℝ) (k : ℕ) :
    Function.Injective (primeExteriorEmbedding δ k) :=
  ((HilbertSchmidt.lpBasis (PrimeFaceIndex k)).orthonormal.linearIndependent.finsuppLinearCombination_injective.comp (primeChainBasis ℂ k).repr.injective).comp
      (dirichletChainGaugeEquiv ((δ/2:ℝ):ℂ) k).injective

/-- Finite exterior chains are dense for every conductor weight and exterior degree. -/
theorem primeExteriorEmbedding_dense (δ : ℝ) (k : ℕ) :
    DenseRange (primeExteriorEmbedding δ k) := by
  have he : Set.range (primeExteriorEmbedding δ k)=
      Set.range (Finsupp.linearCombination ℂ (HilbertSchmidt.lpBasis (PrimeFaceIndex k))) := by
    ext u
    constructor
    · rintro ⟨a,rfl⟩
      exact ⟨(primeChainBasis ℂ k).repr (dirichletChainGauge ((δ/2:ℝ):ℂ) k a),rfl⟩
    · rintro ⟨c,rfl⟩
      obtain ⟨a,ha⟩:=(dirichletChainGaugeEquiv ((δ/2:ℝ):ℂ) k).surjective
        ((primeChainBasis ℂ k).repr.symm c)
      change dirichletChainGauge ((δ/2:ℝ):ℂ) k a = _ at ha
      refine ⟨a,?_⟩
      change Finsupp.linearCombination ℂ _
        ((primeChainBasis ℂ k).repr (dirichletChainGauge ((δ/2:ℝ):ℂ) k a))=_
      rw [ha,LinearEquiv.apply_symm_apply]
  change Dense (Set.range (primeExteriorEmbedding δ k))
  rw [he]
  change Dense ((LinearMap.range (Finsupp.linearCombination ℂ
    (HilbertSchmidt.lpBasis (PrimeFaceIndex k))) : Submodule ℂ (PrimeExteriorHilbert k)) :
      Set (PrimeExteriorHilbert k))
  rw [Submodule.dense_iff_topologicalClosure_eq_top,Finsupp.range_linearCombination]
  exact (HilbertSchmidt.lpBasis (PrimeFaceIndex k)).dense_span

/-- The shifted boundary intertwines with the same actual gauge in adjacent exterior degrees. -/
theorem dirichletChainGauge_shift_boundary (s z : ℂ) (k : ℕ) :
    (dirichletPrimeChainBoundary k (s+z)).comp (dirichletChainGauge z (k+1))=
      (dirichletChainGauge z k).comp (dirichletPrimeChainBoundary k s) := by
  exact HTGeometry.physicalKoszulDifferential_natural k (dirichletVertexGauge z)
    (dirichletPrimeChainFunctional (s+z)) (dirichletPrimeChainFunctional s)
    (by simpa only [add_sub_cancel_right] using primeBoundary_gauge_shift (s+z) z)

/-- The graph of the original finite boundary in the prescribed weighted Hilbert carriers. -/
def primeExteriorBoundaryGraph (δ : ℝ) (s : ℂ) (k : ℕ) :
    Set (PrimeExteriorHilbert (k+1) × PrimeExteriorHilbert k) :=
  Set.range (fun a : PrimeChainSpace ℂ (k+1)=>
    (primeExteriorEmbedding δ (k+1) a,
      primeExteriorEmbedding δ k (dirichletPrimeChainBoundary k s a)))

/-- The unitary gauge on adjacent degrees, viewed as a homeomorphism of graph carriers. -/
def primeExteriorGraphGauge (t : ℝ) (k : ℕ) :
    (PrimeExteriorHilbert (k+1) × PrimeExteriorHilbert k) ≃ₜ
      (PrimeExteriorHilbert (k+1) × PrimeExteriorHilbert k) :=
  (primeExteriorUnitary t (k+1)).toHomeomorph.prodCongr (primeExteriorUnitary t k).toHomeomorph

/-- The graph gauge sends each finite arithmetic boundary pair to its shifted pair. -/
theorem primeExteriorGraphGauge_finite (δ t : ℝ) (s : ℂ) (k : ℕ)
    (a : PrimeChainSpace ℂ (k+1)) :
    primeExteriorGraphGauge t k
      (primeExteriorEmbedding δ (k+1) a,
        primeExteriorEmbedding δ k (dirichletPrimeChainBoundary k s a))=
      (primeExteriorEmbedding δ (k+1) (dirichletChainGauge ((t:ℂ)*Complex.I) (k+1) a),
        primeExteriorEmbedding δ k (dirichletPrimeChainBoundary k (s+(t:ℂ)*Complex.I)
          (dirichletChainGauge ((t:ℂ)*Complex.I) (k+1) a))) := by
  apply Prod.ext
  · exact LinearMap.congr_fun (primeExteriorUnitary_finite δ t (k+1)) a
  · change primeExteriorUnitary t k
      (primeExteriorEmbedding δ k (dirichletPrimeChainBoundary k s a))=_
    have hu := LinearMap.congr_fun (primeExteriorUnitary_finite δ t k)
      (dirichletPrimeChainBoundary k s a)
    change primeExteriorUnitary t k
      (primeExteriorEmbedding δ k (dirichletPrimeChainBoundary k s a)) =
      primeExteriorEmbedding δ k (dirichletChainGauge ((t:ℂ)*Complex.I) k
        (dirichletPrimeChainBoundary k s a)) at hu
    rw [hu]
    exact congrArg (primeExteriorEmbedding δ k)
      (LinearMap.congr_fun (dirichletChainGauge_shift_boundary s ((t:ℂ)*Complex.I) k) a).symm

/-- Every finite boundary graph is unitarily equivalent to its vertical translate. -/
theorem primeExteriorBoundaryGraph_vertical (δ t : ℝ) (s : ℂ) (k : ℕ) :
    (primeExteriorGraphGauge t k) '' primeExteriorBoundaryGraph δ s k=
      primeExteriorBoundaryGraph δ (s+(t:ℂ)*Complex.I) k := by
  ext y
  constructor
  · rintro ⟨z,⟨a,rfl⟩,rfl⟩
    rw [primeExteriorGraphGauge_finite]
    exact ⟨dirichletChainGauge ((t:ℂ)*Complex.I) (k+1) a,rfl⟩
  · rintro ⟨a,rfl⟩
    obtain ⟨b,hb⟩:=(dirichletChainGaugeEquiv ((t:ℂ)*Complex.I) (k+1)).surjective a
    change dirichletChainGauge ((t:ℂ)*Complex.I) (k+1) b = a at hb
    refine ⟨(primeExteriorEmbedding δ (k+1) b,
      primeExteriorEmbedding δ k (dirichletPrimeChainBoundary k s b)),⟨b,rfl⟩,?_⟩
    rw [primeExteriorGraphGauge_finite,hb]

/-- Graph closure preserves the exact vertical unitary equivalence without a closability premise. -/
theorem primeExteriorBoundaryClosure_vertical (δ t : ℝ) (s : ℂ) (k : ℕ) :
    (primeExteriorGraphGauge t k) '' closure (primeExteriorBoundaryGraph δ s k)=
      closure (primeExteriorBoundaryGraph δ (s+(t:ℂ)*Complex.I) k) := by
  rw [(primeExteriorGraphGauge t k).image_closure,primeExteriorBoundaryGraph_vertical]

/-- Up to the explicit unitary gauge, the completed boundary relation depends only on the real part. -/
theorem primeExteriorBoundaryClosure_realPart (δ : ℝ) (s : ℂ) (k : ℕ) :
    (primeExteriorGraphGauge s.im k) '' closure (primeExteriorBoundaryGraph δ (s.re:ℂ) k)=
      closure (primeExteriorBoundaryGraph δ s k) := by
  simpa only [Complex.re_add_im] using
    primeExteriorBoundaryClosure_vertical δ s.im (s.re:ℂ) k

#print axioms primeExteriorEmbedding_norm_sq
#print axioms dirichletChainGauge_basis
#print axioms primeFaceMultiplier_imag_norm
#print axioms primeExteriorUnitary_finite
#print axioms primeExteriorEmbedding_injective
#print axioms primeExteriorEmbedding_dense
#print axioms dirichletChainGauge_shift_boundary
#print axioms primeExteriorBoundaryGraph_vertical
#print axioms primeExteriorBoundaryClosure_vertical
#print axioms primeExteriorBoundaryClosure_realPart
end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
