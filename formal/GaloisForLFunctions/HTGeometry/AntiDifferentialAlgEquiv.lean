import GaloisForLFunctions.HTGeometry.KolchinExchangeGaugeObstruction

/-!
# Orientation-reversing differential automorphisms

The rapidity reflection `f(θ) ↦ f(−θ)` is a field automorphism that *anti*-commutes with the
derivation, so it is not a `DifferentialAlgEquiv`.  It still preserves differential algebraicity:
its `n`-th jet picks up the sign `(−1)^n`, and rescaling the jet variables of a multivariate
polynomial by units is an automorphism of the polynomial algebra.

* `algebraicIndependent_smul_units_iff` — algebraic independence is invariant under rescaling each
  member by a unit of the base;
* `AntiDifferentialAlgEquiv` and `AntiDifferentialAlgEquiv.differentialAlgebraicOver_map_iff` —
  the anti-commuting analogue of the Kolchin transport lemma.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

noncomputable section

/-! ## Rescaling variables by units -/

theorem algebraicIndependent_smul_units_iff {ι F E : Type*} [CommRing F] [CommRing E]
    [Algebra F E] (c : ι → Fˣ) (v : ι → E) :
    AlgebraicIndependent F (fun i => ((c i : F)) • v i) ↔ AlgebraicIndependent F v := by
  classical
  set Φ : MvPolynomial ι F →ₐ[F] MvPolynomial ι F :=
    MvPolynomial.aeval (fun i => ((c i : F)) • MvPolynomial.X i) with hΦ
  set Ψ : MvPolynomial ι F →ₐ[F] MvPolynomial ι F :=
    MvPolynomial.aeval (fun i => (((c i)⁻¹ : Fˣ) : F) • MvPolynomial.X i) with hΨ
  have hΦΨ : Φ.comp Ψ = AlgHom.id F (MvPolynomial ι F) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, hΦ, hΨ, MvPolynomial.aeval_X, AlgHom.id_apply, map_smul]
    rw [smul_smul]
    simp
  have hΨΦ : Ψ.comp Φ = AlgHom.id F (MvPolynomial ι F) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, hΦ, hΨ, MvPolynomial.aeval_X, AlgHom.id_apply, map_smul]
    rw [smul_smul]
    simp
  have hΦsurj : Function.Surjective Φ := fun p =>
    ⟨Ψ p, by rw [← AlgHom.comp_apply, hΦΨ, AlgHom.id_apply]⟩
  have hΦinj : Function.Injective Φ := by
    intro p q hpq
    have := congrArg Ψ hpq
    rwa [← AlgHom.comp_apply, ← AlgHom.comp_apply, hΨΦ, AlgHom.id_apply, AlgHom.id_apply] at this
  have hfact : (MvPolynomial.aeval fun i => ((c i : F)) • v i)
      = (MvPolynomial.aeval v).comp Φ := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [hΦ]
  constructor
  · intro hind
    rw [AlgebraicIndependent] at hind ⊢
    intro p q hpq
    have hΦp : Φ p = Φ q → p = q := fun h => hΦinj h
    obtain ⟨p', rfl⟩ := hΦsurj p
    obtain ⟨q', rfl⟩ := hΦsurj q
    have : (MvPolynomial.aeval fun i => ((c i : F)) • v i) p'
        = (MvPolynomial.aeval fun i => ((c i : F)) • v i) q' := by
      rw [hfact, AlgHom.comp_apply, AlgHom.comp_apply]
      exact hpq
    exact congrArg Φ (hind this)
  · intro hind
    rw [AlgebraicIndependent] at hind ⊢
    intro p q hpq
    rw [hfact, AlgHom.comp_apply, AlgHom.comp_apply] at hpq
    exact hΦinj (hind hpq)

/-- The sign `(−1)^n` as a unit of the base field. -/
def signUnit {F : Type*} [Field F] (n : ℕ) : Fˣ := (-1 : Fˣ) ^ n

theorem signUnit_coe {F : Type*} [Field F] (n : ℕ) : ((signUnit (F := F) n : Fˣ) : F) = (-1) ^ n := by
  rw [signUnit, Units.val_pow_eq_pow_val]
  norm_num

theorem signUnit_smul {F E : Type*} [Field F] [Field E] [Algebra F E] (n : ℕ) (y : E) :
    ((signUnit (F := F) n : Fˣ) : F) • y = (-1 : E) ^ n * y := by
  rw [signUnit_coe, Algebra.smul_def, map_pow, map_neg, map_one]

/-! ## Anti-differential automorphisms -/

/-- A coefficient-fixing field automorphism that anti-commutes with the derivation, as the
rapidity reflection `f(θ) ↦ f(−θ)` does. -/
structure AntiDifferentialAlgEquiv (F E : Type*) [Field F] [Field E] [Algebra F E]
    [Differential E] extends E ≃ₐ[F] E where
  map_deriv_neg' : ∀ x, toAlgEquiv x′ = -((toAlgEquiv x)′)

namespace AntiDifferentialAlgEquiv

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]

/-- The inverse of an orientation-reversing differential automorphism is again one. -/
def symm (σ : AntiDifferentialAlgEquiv F E) : AntiDifferentialAlgEquiv F E where
  toAlgEquiv := σ.toAlgEquiv.symm
  map_deriv_neg' x := by
    apply σ.toAlgEquiv.injective
    rw [map_neg, σ.toAlgEquiv.apply_symm_apply, σ.map_deriv_neg',
      σ.toAlgEquiv.apply_symm_apply, neg_neg]

@[simp]
theorem symm_toAlgEquiv (σ : AntiDifferentialAlgEquiv F E) :
    σ.symm.toAlgEquiv = σ.toAlgEquiv.symm := rfl

/-- The `n`-th jet is transported with the sign `(−1)^n`. -/
theorem map_differentialJet (σ : AntiDifferentialAlgEquiv F E) (n : ℕ) (x : E) :
    σ.toAlgEquiv (differentialJet n x) = (-1 : E) ^ n * differentialJet n (σ.toAlgEquiv x) := by
  have hneg : ∀ y : E, (-y)′ = -(y′) := fun y => Derivation.map_neg Differential.deriv y
  induction n with
  | zero => simp [differentialJet]
  | succ n ih =>
      rw [differentialJet_succ, σ.map_deriv_neg', ih, differentialJet_succ]
      rcases Nat.even_or_odd n with hn | hn
      · rw [hn.neg_one_pow, one_mul, Odd.neg_one_pow (Even.add_one hn), neg_one_mul]
      · rw [hn.neg_one_pow, Even.neg_one_pow (Odd.add_one hn), one_mul, neg_one_mul,
          hneg, neg_neg]

/-- **Orientation-reversing transport of differential algebraicity.**  An automorphism that
anti-commutes with the derivation preserves differential algebraicity exactly. -/
theorem differentialAlgebraicOver_map_iff (σ : AntiDifferentialAlgEquiv F E) (x : E) :
    DifferentialAlgebraicOver F (σ.toAlgEquiv x) ↔ DifferentialAlgebraicOver F x := by
  have hkey : ∀ y : E, AlgebraicIndependent F (fun p : Unit × ℕ => differentialJet p.2 y)
      ↔ AlgebraicIndependent F (fun p : Unit × ℕ => differentialJet p.2 (σ.toAlgEquiv y)) := by
    intro y
    have hsign : ∀ p : Unit × ℕ,
        σ.toAlgEquiv (differentialJet p.2 y)
          = (-1 : E) ^ p.2 * differentialJet p.2 (σ.toAlgEquiv y) :=
      fun p => σ.map_differentialJet p.2 y
    constructor
    · intro hind
      have himg : AlgebraicIndependent F
          (fun p : Unit × ℕ => σ.toAlgEquiv (differentialJet p.2 y)) :=
        hind.map (f := σ.toAlgEquiv.toAlgHom) σ.toAlgEquiv.injective.injOn
      have hrw : (fun p : Unit × ℕ => σ.toAlgEquiv (differentialJet p.2 y))
          = fun p : Unit × ℕ =>
            ((signUnit (F := F) p.2 : F)) • differentialJet p.2 (σ.toAlgEquiv y) := by
        funext p
        rw [hsign p, signUnit_smul]
      rw [hrw] at himg
      exact (algebraicIndependent_smul_units_iff
        (fun p : Unit × ℕ => signUnit (F := F) p.2) _).mp himg
    · intro hind
      have hscaled : AlgebraicIndependent F
          (fun p : Unit × ℕ => ((signUnit (F := F) p.2 : F)) •
            differentialJet p.2 (σ.toAlgEquiv y)) :=
        (algebraicIndependent_smul_units_iff
          (fun p : Unit × ℕ => signUnit (F := F) p.2) _).mpr hind
      have hrw : (fun p : Unit × ℕ =>
          ((signUnit (F := F) p.2 : F)) • differentialJet p.2 (σ.toAlgEquiv y))
            = ⇑σ.toAlgEquiv.toAlgHom ∘ fun p : Unit × ℕ => differentialJet p.2 y := by
        funext p
        show ((signUnit (F := F) p.2 : F)) • differentialJet p.2 (σ.toAlgEquiv y)
          = σ.toAlgEquiv (differentialJet p.2 y)
        rw [signUnit_smul, ← hsign p]
      rw [hrw] at hscaled
      exact hscaled.of_comp σ.toAlgEquiv.toAlgHom
  constructor
  · intro hs hx
    exact hs (by simpa [DifferentialIndependent] using (hkey x).mp (by simpa [DifferentialIndependent] using hx))
  · intro hx hs
    exact hx (by simpa [DifferentialIndependent] using (hkey x).mpr (by simpa [DifferentialIndependent] using hs))

end AntiDifferentialAlgEquiv

/-! ## The Kolchin exchange obstruction for an orientation-reversing gauge -/

/-- Differential-algebraic exchange-gauge equivalence across an orientation-reversing
automorphism: `T = σ(g)·S/g` for a nonzero differentially algebraic multiplier. -/
def AntiDAExchangeGaugeEquivalent
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    (σ : AntiDifferentialAlgEquiv F E) (S T : E) : Prop :=
  ∃ g : E, g ≠ 0 ∧ DifferentialAlgebraicOver F g ∧
    T = σ.toAlgEquiv g * S / g

variable {F E : Type*} [Field F] [Field E] [Algebra F E]
  [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]

theorem differentialAlgebraicOver_ratio_of_antiDAExchangeGaugeEquivalent
    (σ : AntiDifferentialAlgEquiv F E) {S T : E} (hS : S ≠ 0)
    (h : AntiDAExchangeGaugeEquivalent σ S T) :
    DifferentialAlgebraicOver F (T / S) := by
  obtain ⟨g, hg0, hg, rfl⟩ := h
  have hσg : DifferentialAlgebraicOver F (σ.toAlgEquiv g) :=
    (σ.differentialAlgebraicOver_map_iff g).mpr hg
  have hratio := differentialAlgebraicOver_div hσg hg
  convert hratio using 1
  field_simp

/-- **Kolchin exchange obstruction, orientation-reversing form.** -/
theorem not_antiDAExchangeGaugeEquivalent_of_ratio_hypertranscendental
    (σ : AntiDifferentialAlgEquiv F E) {S T : E} (hS : S ≠ 0)
    (hHT : ¬ DifferentialAlgebraicOver F (T / S)) :
    ¬ AntiDAExchangeGaugeEquivalent σ S T := fun h =>
  hHT (differentialAlgebraicOver_ratio_of_antiDAExchangeGaugeEquivalent σ hS h)

theorem differentialAlgebraicOver_exchangeLaw_of_antiSection
    (σ : AntiDifferentialAlgEquiv F E) {S f : E} (hf0 : f ≠ 0)
    (hf : DifferentialAlgebraicOver F f)
    (hexchange : σ.toAlgEquiv f = S * f) :
    DifferentialAlgebraicOver F S := by
  have hσf : DifferentialAlgebraicOver F (σ.toAlgEquiv f) :=
    (σ.differentialAlgebraicOver_map_iff f).mpr hf
  have hratio := differentialAlgebraicOver_div hσf hf
  convert hratio using 1
  rw [hexchange]
  field_simp

/-- **Exchange-section forcing.**  Every nonzero section of a hypertranscendental exchange law is
hypertranscendental, also for an orientation-reversing gauge. -/
theorem antiSection_hypertranscendental_of_exchangeLaw
    (σ : AntiDifferentialAlgEquiv F E) {S f : E} (hf0 : f ≠ 0)
    (hSHT : ¬ DifferentialAlgebraicOver F S)
    (hexchange : σ.toAlgEquiv f = S * f) :
    ¬ DifferentialAlgebraicOver F f := fun hf =>
  hSHT (differentialAlgebraicOver_exchangeLaw_of_antiSection σ hf0 hf hexchange)

theorem no_antiDAExchangeGauge_trivialization_of_hypertranscendental
    (σ : AntiDifferentialAlgEquiv F E) {S : E} (hS0 : S ≠ 0)
    (hSHT : ¬ DifferentialAlgebraicOver F S) (c : F) (hc : c ≠ 0) :
    ¬ AntiDAExchangeGaugeEquivalent σ S (algebraMap F E c) := by
  apply not_antiDAExchangeGaugeEquivalent_of_ratio_hypertranscendental σ hS0
  exact ((differentialAlgebraicOver_const_div_iff c hc S).not).mpr hSHT

/-- **The half-phase law across the reflection.**  Every `y` with `S = c·y/σ(y)` is
hypertranscendental whenever `S` is. -/
theorem antiHalfPhase_hypertranscendental_of_exchangeLaw
    (σ : AntiDifferentialAlgEquiv F E) {S y : E} (hS0 : S ≠ 0)
    (hSHT : ¬ DifferentialAlgebraicOver F S) (c : F) (hc : c ≠ 0)
    (hy0 : y ≠ 0)
    (hS : S = algebraMap F E c * y / σ.toAlgEquiv y) :
    ¬ DifferentialAlgebraicOver F y := by
  intro hy
  apply no_antiDAExchangeGauge_trivialization_of_hypertranscendental σ hS0 hSHT c hc
  refine ⟨y, hy0, hy, ?_⟩
  rw [hS]
  field_simp [hy0]


end

end GaloisForLFunctions.HTGeometry
