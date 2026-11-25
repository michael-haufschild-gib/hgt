import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.IntegerPolynomialGrading
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.PolynomialCoefficientDescent
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.MatrixChartWitnesses
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.FormalSmoothQuotientWitnesses
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.FlatSpecializedCokernel
import Mathlib.RingTheory.Smooth.Flat

/-! Finite witnesses descend a homogeneous presentation and preserve flatness on each chart. -/

noncomputable section

open MvPolynomial

namespace GlobalTheory.SmoothDescent

/-- A homogeneous presentation with smooth coefficient algebras and projective
chart modules descends over a Noetherian subalgebra with flat specialized cokernels. -/
theorem exists_noetherian_matrix_model {ι R : Type} [Fintype ι] [CommRing R] {a b : ℕ}
    (d : Fin a → ℤ) (e : Fin b → ℤ) (Φ : Matrix (Fin a) (Fin b) (MvPolynomial ι R))
    (hΦ : ∀ l j, Φ l j ∈ polyGrading ι R (e j - d l))
    (hChart : ∀ i : ι, ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B)
      (π : MvPolynomial ι R →ₐ[R] B) (P : Type) (_ : AddCommGroup P) (_ : Module B P)
      (ε : (Fin a → MvPolynomial ι R) →ₛₗ[π.toRingHom] P),
      Algebra.Smooth R B ∧ Module.Projective B P ∧ Function.Surjective π ∧ π (X i) = 1 ∧
        Function.Surjective ε ∧
          ∀ y, ε y = 0 ↔ ∃ w w', y = Φ.mulVec w + (X i - 1 : MvPolynomial ι R) • w') :
    ∃ (R₀ : Subalgebra ℤ R) (_ : IsNoetherianRing R₀)
      (Φ₀ : Matrix (Fin a) (Fin b) (MvPolynomial ι R₀)),
      Φ₀.map (MvPolynomial.map R₀.val.toRingHom) = Φ ∧
        (∀ l j, Φ₀ l j ∈ polyGrading ι R₀ (e j - d l)) ∧
        ∀ i : ι, Module.Flat R₀ (QuotSMulTop (X i - 1 : MvPolynomial ι R₀)
          ((Fin a → MvPolynomial ι R₀) ⧸ LinearMap.range Φ₀.mulVecLin)) := by
  classical
  have witnesses (i : ι) : ∃ (r : ℕ) (g : Fin r → MvPolynomial ι R),
      Algebra.FormallySmooth R (MvPolynomial ι R ⧸ Ideal.span (Set.range g)) ∧
      (∃ c : Fin r → MvPolynomial ι R, (X i - 1 : MvPolynomial ι R) = ∑ k, c k * g k) ∧
      (∀ k, ∃ (C : Matrix (Fin b) (Fin a) (MvPolynomial ι R))
          (C' : Matrix (Fin a) (Fin a) (MvPolynomial ι R)),
        g k • (1 : Matrix (Fin a) (Fin a) (MvPolynomial ι R)) =
          Φ * C + (X i - 1 : MvPolynomial ι R) • C') ∧
      (∃ (Ψ : Matrix (Fin b) (Fin a) (MvPolynomial ι R))
          (E : Fin r → Matrix (Fin a) (Fin b) (MvPolynomial ι R)),
        Φ * Ψ * Φ = Φ + ∑ k, g k • E k) := by
    obtain ⟨B, _, _, π, P, _, _, ε, hSmooth, hProjective, hπ, hX, hε, hker⟩ := hChart i
    letI := hSmooth
    letI := hProjective
    have hu : π (X i - 1) = 0 := by rw [map_sub, hX, map_one, sub_self]
    exact exists_chart_witnesses Φ (X i - 1) π hπ hu ε hε hker
  choose r g hsm hc hC hΨ using witnesses
  choose wa wb hwit using fun i => exists_witnesses_of_formallySmooth_quotient (g i) (hsm i)
  choose c hc' using hc
  choose C C' hCC using hC
  choose Ψ E hΨE using hΨ
  let Data :=
    (Fin a × Fin b) ⊕ (Σ i, Fin (r i)) ⊕ (Σ i, ι × Fin (r i)) ⊕
    (Σ i, Fin (r i) × Fin (r i) × Fin (r i)) ⊕ (Σ i, Fin (r i)) ⊕
    (Σ i, Fin (r i) × Fin b × Fin a) ⊕ (Σ i, Fin (r i) × Fin a × Fin a) ⊕
    (Σ i, Fin b × Fin a) ⊕ (Σ i, Fin (r i) × Fin a × Fin b)
  let pols : Data → MvPolynomial ι R
    | .inl (l, j) => Φ l j
    | .inr (.inl ⟨i, k⟩) => g i k
    | .inr (.inr (.inl ⟨i, v, k⟩)) => wa i v k
    | .inr (.inr (.inr (.inl ⟨i, j, k, l⟩))) => wb i j k l
    | .inr (.inr (.inr (.inr (.inl ⟨i, k⟩)))) => c i k
    | .inr (.inr (.inr (.inr (.inr (.inl ⟨i, k, j, m⟩))))) => C i k j m
    | .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨i, k, l, m⟩)))))) => C' i k l m
    | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨i, j, m⟩))))))) => Ψ i j m
    | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨i, k, l, j⟩))))))) => E i k l j
  haveI : Finite Data := by
    dsimp only [Data]
    infer_instance
  obtain ⟨R₀, hnoeth, L, hL⟩ := exists_noetherian_polynomial_model pols
  letI := hnoeth
  let φ : MvPolynomial ι R₀ →+* MvPolynomial ι R := MvPolynomial.map R₀.val.toRingHom
  have hφinj : Function.Injective φ := MvPolynomial.map_injective _ Subtype.val_injective
  let Φ₀ : Matrix (Fin a) (Fin b) (MvPolynomial ι R₀) := Matrix.of fun l j => L (Sum.inl (l, j))
  let g₀ : ∀ i, Fin (r i) → MvPolynomial ι R₀ := fun i k => L (Sum.inr (Sum.inl ⟨i, k⟩))
  let wa₀ : ∀ i, ι → Fin (r i) → MvPolynomial ι R₀ := fun i v k =>
    L (Sum.inr (Sum.inr (Sum.inl ⟨i, v, k⟩)))
  let wb₀ : ∀ i, Fin (r i) → Fin (r i) → Fin (r i) → MvPolynomial ι R₀ := fun i j k l =>
    L (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨i, j, k, l⟩))))
  let c₀ : ∀ i, Fin (r i) → MvPolynomial ι R₀ := fun i k =>
    L (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨i, k⟩)))))
  let C₀ : ∀ i, Fin (r i) → Matrix (Fin b) (Fin a) (MvPolynomial ι R₀) := fun i k => Matrix.of fun j m =>
    L (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨i, k, j, m⟩))))))
  let C'₀ : ∀ i, Fin (r i) → Matrix (Fin a) (Fin a) (MvPolynomial ι R₀) := fun i k => Matrix.of fun l m =>
    L (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨i, k, l, m⟩)))))))
  let Ψ₀ : ∀ i, Matrix (Fin b) (Fin a) (MvPolynomial ι R₀) := fun i => Matrix.of fun j m =>
    L (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨i, j, m⟩))))))))
  let E₀ : ∀ i, Fin (r i) → Matrix (Fin a) (Fin b) (MvPolynomial ι R₀) := fun i k => Matrix.of fun l j =>
    L (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr ⟨i, k, l, j⟩))))))))
  have hΦ₀ : ∀ l j, φ (Φ₀ l j) = Φ l j := fun l j => hL _
  have hg₀ : ∀ i k, φ (g₀ i k) = g i k := fun i k => hL _
  have hwa₀ : ∀ i v k, φ (wa₀ i v k) = wa i v k := fun i v k => hL _
  have hwb₀ : ∀ i j k l, φ (wb₀ i j k l) = wb i j k l := fun i j k l => hL _
  have hc₀ : ∀ i k, φ (c₀ i k) = c i k := fun i k => hL _
  have hC₀ : ∀ i k j m, φ (C₀ i k j m) = C i k j m := fun i k j m => hL _
  have hC'₀ : ∀ i k l m, φ (C'₀ i k l m) = C' i k l m := fun i k l m => hL _
  have hΨ₀ : ∀ i j m, φ (Ψ₀ i j m) = Ψ i j m := fun i j m => hL _
  have hE₀ : ∀ i k l j, φ (E₀ i k l j) = E i k l j := fun i k l j => hL _
  have hφX : ∀ v, φ (X v) = X v := fun v => MvPolynomial.map_X _ _
  refine ⟨R₀, hnoeth, Φ₀, ?_, ?_, ?_⟩
  · exact Matrix.ext fun l j => hΦ₀ l j
  · intro l j
    rw [GlobalTheory.mem_polyGrading_iff]
    intro α hα
    refine (GlobalTheory.mem_polyGrading_iff.1 (hΦ l j)) α ?_
    rw [← hΦ₀ l j, MvPolynomial.coeff_map]
    intro h0
    exact hα (Subtype.val_injective (by simpa using h0))
  · intro i
    have hwit₀ : ∀ j, aeval (fun v => X v + ∑ k, wa₀ i v k * g₀ i k) (g₀ i j) =
        ∑ k, ∑ l, wb₀ i j k l * (g₀ i k * g₀ i l) := by
      intro j
      apply hφinj
      rw [aeval_eq_bind₁, MvPolynomial.map_bind₁]
      simp only [φ] at hg₀ hwa₀ hwb₀ hφX ⊢
      simp only [map_add, map_sum, map_mul, hg₀, hwa₀, hwb₀, hφX]
      rw [← aeval_eq_bind₁]
      exact hwit i j
    haveI : Algebra.FormallySmooth R₀ (MvPolynomial ι R₀ ⧸ Ideal.span (Set.range (g₀ i))) :=
      formallySmooth_quotient_of_aeval_shift_mem_sq (g₀ i) (wa₀ i) (wb₀ i) hwit₀
    haveI : Algebra.FinitePresentation R₀ (MvPolynomial ι R₀ ⧸ Ideal.span (Set.range (g₀ i))) :=
      Algebra.FinitePresentation.of_finiteType.1 inferInstance
    haveI : Algebra.Smooth R₀ (MvPolynomial ι R₀ ⧸ Ideal.span (Set.range (g₀ i))) :=
      ⟨inferInstance, inferInstance⟩
    refine flat_specialized_cokernel (g₀ i)
      (X i - 1) Φ₀ inferInstance ⟨c₀ i, ?_⟩ (fun k => ⟨C₀ i k, C'₀ i k, ?_⟩) ⟨Ψ₀ i, E₀ i, ?_⟩
    · apply hφinj
      simp only [map_sub, map_one, map_sum, map_mul, hc₀, hg₀, hφX]
      exact hc' i
    · refine Matrix.ext fun l m => ?_
      apply hφinj
      have h1 := congr_fun (congr_fun (hCC i k) l) m
      simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.one_apply,
        smul_eq_mul] at h1 ⊢
      simp only [map_add, map_mul, map_sum, map_sub, map_one, hg₀, hφX, hΦ₀, hC₀, hC'₀,
        apply_ite φ, map_zero, map_one]
      simpa [Φ₀, C₀, C'₀] using h1
    · refine Matrix.ext fun l j => ?_
      apply hφinj
      have h1 := congr_fun (congr_fun (hΨE i) l) j
      simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply,
        smul_eq_mul] at h1 ⊢
      simp only [map_add, map_mul, map_sum, hΦ₀, hΨ₀, hE₀, hg₀]
      exact h1

end GlobalTheory.SmoothDescent
