import GaloisForLFunctions.HTGeometry.ConstitutiveInteractionSpectrumMechanics

/-!
# Constitutive essential-formation mechanics

Formation phase is retained modulo summable work.  This is the properness analogue of passing from
an operator to its essential class: finite and summable compensators may alter finite observations,
but cannot change whether total formation work is admitted.  The prime interaction formation and
its reciprocal reflection have the same essential class exactly at exponent one.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Two formation ledgers are essentially equivalent when their difference has summable work. -/
def EssentialFormationEquivalent {ι : Type*} (a b : ι → ℝ) : Prop :=
  Summable fun i => a i - b i

theorem essentialFormationEquivalent_refl {ι : Type*} (a : ι → ℝ) :
    EssentialFormationEquivalent a a := by
  unfold EssentialFormationEquivalent
  simpa only [sub_self] using (summable_zero : Summable fun _i : ι => (0 : ℝ))

theorem essentialFormationEquivalent_symm {ι : Type*} {a b : ι → ℝ}
    (h : EssentialFormationEquivalent a b) :
    EssentialFormationEquivalent b a := by
  unfold EssentialFormationEquivalent at h ⊢
  exact h.neg.congr fun i => by ring

theorem essentialFormationEquivalent_trans {ι : Type*} {a b c : ι → ℝ}
    (hab : EssentialFormationEquivalent a b)
    (hbc : EssentialFormationEquivalent b c) :
    EssentialFormationEquivalent a c := by
  unfold EssentialFormationEquivalent at hab hbc ⊢
  exact hab.add hbc |>.congr fun i => by ring

/-- Essential equivalence preserves the admitted/summable formation phase. -/
theorem summable_iff_of_essentialFormationEquivalent
    {ι : Type*} {a b : ι → ℝ}
    (h : EssentialFormationEquivalent a b) :
    Summable a ↔ Summable b := by
  unfold EssentialFormationEquivalent at h
  constructor
  · intro ha
    exact ha.sub h |>.congr fun i => by ring
  · intro hb
    exact hb.add h |>.congr fun i => by ring

/-- Every finite-support correction is inessential. -/
theorem essentialFormationEquivalent_of_finiteSupport
    {ι : Type*} {a b : ι → ℝ}
    (h : Function.HasFiniteSupport fun i => a i - b i) :
    EssentialFormationEquivalent a b := by
  exact summable_of_hasFiniteSupport h

/-- **Essential reciprocal selection.**  On the physical strip, the literal prime interaction
formation and its reciprocal reflection differ by summable work exactly at the fixed point. -/
theorem primeInteractionEssentialReflection_iff
    {σ : ℝ} (hσ0 : 0 < σ) (hσ2 : σ < 2) :
    EssentialFormationEquivalent (primeInteractionActivation σ)
      (primeInteractionActivation (2 - σ)) ↔ σ = 1 := by
  constructor
  · intro hessential
    apply (primeInteractionFormationPhase_reflection_iff hσ0 hσ2).mp
    exact summable_iff_of_essentialFormationEquivalent hessential
  · intro hσ
    subst σ
    unfold EssentialFormationEquivalent
    have htwo : (2 : ℝ) - 1 = 1 := by linarith
    have hzero : (fun p : Nat.Primes =>
        primeInteractionActivation 1 p - primeInteractionActivation (2 - 1) p) =
        fun _p => 0 := by
      simp only [htwo, sub_self]
    rw [hzero]
    exact summable_zero

/-- Off the fixed point, no finite-work or summable compensator can implement reciprocal
formation matching. -/
theorem not_primeInteractionEssentialReflection_of_ne
    {σ : ℝ} (hσ0 : 0 < σ) (hσ2 : σ < 2) (hσ1 : σ ≠ 1) :
    ¬ EssentialFormationEquivalent (primeInteractionActivation σ)
      (primeInteractionActivation (2 - σ)) := by
  intro h
  exact hσ1 ((primeInteractionEssentialReflection_iff hσ0 hσ2).mp h)

/-- Away from the fixed point, reciprocal matching cannot be repaired by adding any summable
formation ledger.  This is the explicit compensator form of essential selection. -/
theorem no_summable_compensator_primeInteractionReflection
    {σ : ℝ} (hσ0 : 0 < σ) (hσ2 : σ < 2) (hσ1 : σ ≠ 1) :
    ¬ ∃ c : Nat.Primes → ℝ, Summable c ∧
      ∀ p, primeInteractionActivation σ p =
        primeInteractionActivation (2 - σ) p + c p := by
  rintro ⟨c, hc, hmatch⟩
  apply not_primeInteractionEssentialReflection_of_ne hσ0 hσ2 hσ1
  unfold EssentialFormationEquivalent
  exact hc.congr fun p => by
    rw [hmatch p]
    ring

/-- **Global bridge consumer.**  A source formation need not equal the prime formation.  Essential
source-to-prime bridges on both reflected fibres, together with an essential source-duality bridge,
already force the reciprocal fixed point. -/
theorem essentialFormationSelection_of_sourceBridge
    (source : ℝ → Nat.Primes → ℝ) {σ : ℝ}
    (hσ0 : 0 < σ) (hσ2 : σ < 2)
    (hleft : EssentialFormationEquivalent
      (primeInteractionActivation σ) (source σ))
    (hduality : EssentialFormationEquivalent (source σ) (source (2 - σ)))
    (hright : EssentialFormationEquivalent
      (source (2 - σ)) (primeInteractionActivation (2 - σ))) :
    σ = 1 := by
  apply (primeInteractionEssentialReflection_iff hσ0 hσ2).mp
  exact essentialFormationEquivalent_trans hleft
    (essentialFormationEquivalent_trans hduality hright)

end

end GaloisForLFunctions.HTGeometry
