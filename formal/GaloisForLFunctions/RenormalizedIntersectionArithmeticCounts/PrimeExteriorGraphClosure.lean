import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.PrimeExteriorTailCoordinates
import GaloisForLFunctions.HTGeometry.BanachTransposeIsomorphism

/-!
# Critical graph closure of the arithmetic exterior boundary

At and below the critical conductor weight, the graph closure of every
exterior boundary is the entire source–target Hilbert product. Continuous
observations are tested on faces with one prime beyond every fixed vertex.
Their tail coordinates are square summable, whereas the Dirichlet coefficients
are not. Every graph annihilator therefore vanishes, and Hahn–Banach supplies
the exact closed relation. The comparison retains the original finite chains.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open RHTower EffectiveScalingGeometry

attribute [local instance] primeLabelLinearOrder

private theorem exteriorObservation_eq_zero {k : ℕ}
    (φ : PrimeExteriorHilbert k →L[ℂ] ℂ)
    (hφ : ∀ a, φ (primeExteriorEmbedding0 k a) = 0) : φ = 0 := by
  apply ContinuousLinearMap.ext
  have hd : DenseRange (primeExteriorEmbedding0 k) := by
    simpa only [primeExteriorEmbedding, Complex.ofReal_zero, zero_div,
      dirichletChainGauge_zero, LinearMap.comp_id] using primeExteriorEmbedding_dense 0 k
  have he : Set.EqOn φ (0 : PrimeExteriorHilbert k →L[ℂ] ℂ)
      (Set.range (primeExteriorEmbedding0 k)) := by
    rintro u ⟨a, rfl⟩
    exact hφ a
  intro u
  exact (closure_minimal he (isClosed_eq φ.continuous continuous_const)) (hd u)

/-- A continuous annihilator of the critical graph vanishes on every target face. -/
theorem primeExteriorBoundary_observation_vanish (s : ℂ) (hs : s.re ≤ 1/2) (k : ℕ)
    (φ : PrimeExteriorHilbert (k+1) →L[ℂ] ℂ)
    (ψ : PrimeExteriorHilbert k →L[ℂ] ℂ)
    (h : ∀ a : PrimeChainSpace ℂ (k+1),
      φ (primeExteriorEmbedding0 (k+1) a) +
        ψ (primeExteriorEmbedding0 k (dirichletPrimeChainBoundary k s a)) = 0)
    (v : Fin k ↪o Nat.Primes) :
    ψ (primeExteriorEmbedding0 k (primeChainAtom ℂ v)) = 0 := by
  cases k with
  | zero =>
      have hv : ∀ i : Fin 0, (v i : ℕ) ≤ 0 := fun i => Fin.elim0 i
      have hm := HilbertSchmidt.memℓp_of_sq
        (primeExterior_tail_functional_summable v 0 hv φ)
      apply primeBoundary_tail_scalar_eq_zero s hs 0
      have he (p : PrimeTail 0) :
          (p.val : ℂ)^(-s) * ψ (primeExteriorEmbedding0 0 (primeChainAtom ℂ v)) =
            -φ (primeExteriorEmbedding0 1 (primeChainAtom ℂ (Fin.snoc v p.val))) := by
        have hh := h (primeChainAtom ℂ (Fin.snoc v p.val))
        rw [dirichletPrimeChainBoundary_zero_tailAtom, map_smul, map_smul,
          smul_eq_mul] at hh
        exact eq_neg_of_add_eq_zero_right hh
      simp_rw [he]
      exact hm.neg
  | succ m =>
      let B := Finset.univ.sup (fun i : Fin (m+1) => (v i : ℕ))
      have hv : ∀ i, (v i : ℕ) ≤ B := fun i => le_sup (f := fun i => (v i : ℕ)) (mem_univ i)
      let A := fun p : PrimeTail B =>
        φ (primeExteriorEmbedding0 (m+2) (primeChainAtom ℂ (Fin.snoc v p.val)))
      let F := fun (i : Fin (m+1)) (p : PrimeTail B) =>
        ψ (primeExteriorEmbedding0 (m+1)
          (primeChainAtom ℂ (Fin.snoc (primeFaceDeletion v i) p.val)))
      let c := ((-1 : ℂ)^(m+1)) *
        ψ (primeExteriorEmbedding0 (m+1) (primeChainAtom ℂ v))
      have hA : Memℓp A 2 := HilbertSchmidt.memℓp_of_sq
        (primeExterior_tail_functional_summable v B hv φ)
      have hF (i : Fin (m+1)) : Memℓp (F i) 2 :=
        HilbertSchmidt.memℓp_of_sq
          (primeExterior_tail_functional_summable (primeFaceDeletion v i) B
            (fun j => hv (i.succAbove j)) ψ)
      have hsum : Memℓp (fun p : PrimeTail B => ∑ i : Fin (m+1),
          (((-1 : ℂ)^(i : ℕ)) * (v i : ℂ)^(-s)) * F i p) 2 := by
        exact Memℓp.finsetSum univ (fun i _ =>
          (hF i).const_smul (((-1 : ℂ)^(i : ℕ)) * (v i : ℂ)^(-s)))
      have he (p : PrimeTail B) : (p.val : ℂ)^(-s)*c =
          -(A p + ∑ i : Fin (m+1),
            (((-1 : ℂ)^(i : ℕ)) * (v i : ℂ)^(-s)) * F i p) := by
        have hh := h (primeChainAtom ℂ (Fin.snoc v p.val))
        rw [dirichletPrimeChainBoundary_tailAtom, map_add, map_sum] at hh
        simp only [map_zsmul, map_smul, smul_eq_mul, zsmul_eq_mul,
          Int.cast_pow, Int.cast_neg, Int.cast_one, map_add, map_sum] at hh
        dsimp only [A, F, c]
        simp only [mul_assoc] at hh ⊢
        linear_combination hh
      have hc : c = 0 := primeBoundary_tail_scalar_eq_zero s hs B c (by
        simp_rw [he]
        exact (hA.add hsum).neg)
      exact (mul_eq_zero.mp hc).resolve_left (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))

/-- Both continuous components of a critical graph annihilator vanish. -/
theorem primeExteriorBoundary_annihilator_eq_zero (s : ℂ) (hs : s.re ≤ 1/2) (k : ℕ)
    (φ : PrimeExteriorHilbert (k+1) →L[ℂ] ℂ)
    (ψ : PrimeExteriorHilbert k →L[ℂ] ℂ)
    (h : ∀ a : PrimeChainSpace ℂ (k+1),
      φ (primeExteriorEmbedding0 (k+1) a) +
        ψ (primeExteriorEmbedding0 k (dirichletPrimeChainBoundary k s a)) = 0) :
    φ = 0 ∧ ψ = 0 := by
  have hψ : ψ = 0 := by
    apply exteriorObservation_eq_zero ψ
    have he : ψ.toLinearMap.comp (primeExteriorEmbedding0 k) = 0 := by
      apply (primeChainBasis ℂ k).ext
      intro S
      simpa only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, LinearMap.zero_apply,
        primeChainBasis_eq_atom] using primeExteriorBoundary_observation_vanish s hs k φ ψ h
          (Set.powersetCard.ofFinEmbEquiv.symm S)
    intro a
    exact LinearMap.congr_fun he a
  refine ⟨exteriorObservation_eq_zero φ (fun a => ?_), hψ⟩
  simpa only [hψ, zero_apply, add_zero] using h a

/-- Boundary pairs of all finite-support exterior chains form a linear relation. -/
def primeExteriorBoundaryRelation0 (s : ℂ) (k : ℕ) :
    Submodule ℂ (PrimeExteriorHilbert (k+1) × PrimeExteriorHilbert k) :=
  LinearMap.range ((primeExteriorEmbedding0 (k+1)).prod
    ((primeExteriorEmbedding0 k).comp (dirichletPrimeChainBoundary k s)))

/-- Conductor normalization shifts the real parameter and retains every finite graph pair. -/
theorem primeExteriorBoundaryGraph_normalized (δ : ℝ) (s : ℂ) (k : ℕ) :
    primeExteriorBoundaryGraph δ s k =
      (primeExteriorBoundaryRelation0 (s+((δ/2:ℝ):ℂ)) k : Set _) := by
  let z : ℂ := ((δ/2:ℝ):ℂ)
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨dirichletChainGauge z (k+1) a, ?_⟩
    apply Prod.ext
    · rfl
    · change primeExteriorEmbedding0 k
        (dirichletPrimeChainBoundary k (s+z) (dirichletChainGauge z (k+1) a)) =
          primeExteriorEmbedding0 k (dirichletChainGauge z k (dirichletPrimeChainBoundary k s a))
      exact congrArg (primeExteriorEmbedding0 k)
        (LinearMap.congr_fun (dirichletChainGauge_shift_boundary s z k) a)
  · rintro ⟨b, rfl⟩
    obtain ⟨a, ha⟩ := (dirichletChainGaugeEquiv z (k+1)).surjective b
    change dirichletChainGauge z (k+1) a = b at ha
    refine ⟨a, ?_⟩
    apply Prod.ext
    · change primeExteriorEmbedding0 (k+1) (dirichletChainGauge z (k+1) a) = _
      rw [ha]
      rfl
    · change primeExteriorEmbedding0 k
        (dirichletChainGauge z k (dirichletPrimeChainBoundary k s a)) =
          primeExteriorEmbedding0 k (dirichletPrimeChainBoundary k (s+z) b)
      rw [← ha]
      exact congrArg (primeExteriorEmbedding0 k)
        (LinearMap.congr_fun (dirichletChainGauge_shift_boundary s z k) a).symm

/-- The finite-support boundary relation is dense in both Hilbert factors at critical weight. -/
theorem primeExteriorBoundaryRelation0_closure (s : ℂ) (hs : s.re ≤ 1/2) (k : ℕ) :
    (primeExteriorBoundaryRelation0 s k).topologicalClosure = ⊤ := by
  let K := primeExteriorBoundaryRelation0 s k
  apply eq_top_iff.mpr
  intro x _
  by_contra hx
  obtain ⟨L, hL, hzero⟩ := HTGeometry.exists_dual_eq_zero_on
    (p := K.topologicalClosure) isClosed_closure hx
  let φ := L.comp (ContinuousLinearMap.inl ℂ (PrimeExteriorHilbert (k+1)) (PrimeExteriorHilbert k))
  let ψ := L.comp (ContinuousLinearMap.inr ℂ (PrimeExteriorHilbert (k+1)) (PrimeExteriorHilbert k))
  have hh (a : PrimeChainSpace ℂ (k+1)) :
      φ (primeExteriorEmbedding0 (k+1) a) +
        ψ (primeExteriorEmbedding0 k (dirichletPrimeChainBoundary k s a)) = 0 := by
    change L (_, 0) + L (0, _) = 0
    rw [← map_add]
    simp only [Prod.mk_add_mk, add_zero, zero_add]
    apply hzero
    apply subset_closure
    exact ⟨a, rfl⟩
  obtain ⟨hφ, hψ⟩ := primeExteriorBoundary_annihilator_eq_zero s hs k φ ψ hh
  apply hL
  apply ContinuousLinearMap.ext
  intro y
  have hleft : L (y.1, 0) = 0 := by
    exact congrArg (fun f : PrimeExteriorHilbert (k+1) →L[ℂ] ℂ => f y.1) hφ
  have hright : L (0, y.2) = 0 := by
    exact congrArg (fun f : PrimeExteriorHilbert k →L[ℂ] ℂ => f y.2) hψ
  calc
    L y = L (y.1, 0) + L (0, y.2) := by
      rw [← map_add]
      apply congrArg L
      ext <;> simp
    _ = 0 := by rw [hleft, hright, zero_add]

/-- Every exterior degree has the whole product as its critical closed boundary relation. -/
theorem primeExteriorBoundaryGraph_closure_eq_univ (δ : ℝ) (s : ℂ) (k : ℕ)
    (h : 2*s.re+δ ≤ 1) :
    closure (primeExteriorBoundaryGraph δ s k) = Set.univ := by
  rw [primeExteriorBoundaryGraph_normalized]
  have hs : (s+((δ/2:ℝ):ℂ)).re ≤ 1/2 := by
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith only [h]
  exact congrArg (fun K : Submodule ℂ (PrimeExteriorHilbert (k+1) × PrimeExteriorHilbert k) =>
    (K : Set (PrimeExteriorHilbert (k+1) × PrimeExteriorHilbert k)))
      (primeExteriorBoundaryRelation0_closure _ hs k)

#print axioms primeExteriorBoundary_observation_vanish
#print axioms primeExteriorBoundary_annihilator_eq_zero
#print axioms primeExteriorBoundaryGraph_normalized
#print axioms primeExteriorBoundaryRelation0_closure
#print axioms primeExteriorBoundaryGraph_closure_eq_univ

end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
