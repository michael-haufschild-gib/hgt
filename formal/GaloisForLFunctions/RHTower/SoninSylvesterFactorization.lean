import GaloisForLFunctions.HTGeometry.DeterminantCompletionNaturality
import GaloisForLFunctions.RHTower.TraceNormLimit
import GaloisForLFunctions.HTGeometry.DisjointSpectrumIntertwiner

/-!
# The Sonin relative-resolvent Sylvester factorization

Let `Q` be the Sonin projection, `G` the pulled-back Euler cyclic density, `R̂_P` the transported
semilocal resolvent and `R_∞` the archimedean resolvent.  If the Sonin space is invariant under
`R̂_P` (`(1-Q) R̂_P Q = 0`) and reduces `R_∞` (`R_∞ Q = Q R_∞ Q`), then the relative-resolvent Sonin
corner is exactly a Sylvester transform of the Euler metric crossing:

```text
(1-Q)(R̂_P G - G R_∞)Q = A_P · H_P - H_P · B_∞,
H_P = (1-Q) G Q,  A_P = (1-Q) R̂_P (1-Q),  B_∞ = Q R_∞ Q.
```

This module proves that identity and its consequences: the transport step through the boundedly
invertible source map, invariance of compactness and of Schatten membership under two-sided
multiplication by invertibles, the Schatten-ideal bound for the corner, and the exact vanishing
criterion.

Everything here is operator algebra: the hypotheses are the quantified data of the theorem, not
analytic inputs.
-/

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The Euler metric crossing `H_P = (1-Q) G Q`. -/
def soninCross (Q G : H →L[ℂ] H) : H →L[ℂ] H := (1 - Q) * G * Q

/-- The restricted outer resolvent `A_P = (1-Q) R (1-Q)`. -/
def soninOuter (Q R : H →L[ℂ] H) : H →L[ℂ] H := (1 - Q) * R * (1 - Q)

/-- The restricted inner resolvent `B_∞ = Q R Q`. -/
def soninInner (Q R : H →L[ℂ] H) : H →L[ℂ] H := Q * R * Q

omit [CompleteSpace H] in
theorem one_sub_idem {Q : H →L[ℂ] H} (hQ : Q * Q = Q) : (1 - Q) * (1 - Q) = 1 - Q := by
  have h : (1 - Q) * (1 - Q) = 1 - Q - Q + Q * Q := by noncomm_ring
  rw [h, hQ]
  abel

omit [CompleteSpace H] in
/-- **The Sonin Sylvester factorization.**  The relative-resolvent Sonin corner is the Sylvester
transform of the Euler metric crossing by the two restricted resolvents. -/
theorem sonin_sylvester_factorization {Q G Rhat Rinf : H →L[ℂ] H}
    (hQ : Q * Q = Q) (hinv : (1 - Q) * Rhat * Q = 0) (hred : Rinf * Q = Q * Rinf * Q) :
    (1 - Q) * (Rhat * G - G * Rinf) * Q
      = soninOuter Q Rhat * soninCross Q G - soninCross Q G * soninInner Q Rinf := by
  have hidem := one_sub_idem hQ
  have hA : soninOuter Q Rhat * soninCross Q G
      = (1 - Q) * Rhat * ((1 - Q) * (1 - Q)) * G * Q := by
    simp only [soninOuter, soninCross]
    noncomm_ring
  rw [hidem] at hA
  have hsplit : (1 - Q) * Rhat * (1 - Q) * G * Q
      = (1 - Q) * (Rhat * G) * Q - ((1 - Q) * Rhat * Q) * (G * Q) := by
    noncomm_ring
  rw [hsplit, hinv, zero_mul, sub_zero] at hA
  have hB : soninCross Q G * soninInner Q Rinf
      = (1 - Q) * G * (Q * Q) * Rinf * Q := by
    simp only [soninCross, soninInner]
    noncomm_ring
  rw [hQ] at hB
  have hB2 : (1 - Q) * G * Q * Rinf * Q = (1 - Q) * G * (Q * Rinf * Q) := by
    noncomm_ring
  rw [hB2, ← hred] at hB
  have hgoal : (1 - Q) * (Rhat * G - G * Rinf) * Q
      = (1 - Q) * (Rhat * G) * Q - (1 - Q) * G * (Rinf * Q) := by
    noncomm_ring
  rw [hgoal, ← hA, ← hB]

/-! ## Transport through the boundedly invertible source map -/

variable {H₂ : Type*} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]

omit [CompleteSpace H] [CompleteSpace H₂] in
/-- **The transport step.**  Pulling the two-space relative resolvent back through the boundedly
invertible source map `θ` turns it into the one-space commutator `R̂ G - G R_∞`. -/
theorem sonin_transport (θ : H ≃L[ℂ] H₂) (RP : H₂ →L[ℂ] H₂) (G Rinf : H →L[ℂ] H) :
    (θ.symm : H₂ →L[ℂ] H) ∘L (RP ∘L ((θ : H →L[ℂ] H₂) ∘L G)
        - ((θ : H →L[ℂ] H₂) ∘L G) ∘L Rinf)
      = ((θ.symm : H₂ →L[ℂ] H) ∘L RP ∘L (θ : H →L[ℂ] H₂)) ∘L G - G ∘L Rinf := by
  ext x
  simp [ContinuousLinearMap.comp_apply]

/-! ## Ideal stability -/

omit [CompleteSpace H] in
/-- **Compactness is invariant under two-sided multiplication by invertibles.** -/
theorem isCompactOperator_equiv_comp_iff (L : H ≃L[ℂ] H) (X : H →L[ℂ] H) :
    IsCompactOperator ((L : H →L[ℂ] H) ∘L X) ↔ IsCompactOperator X := by
  constructor
  · intro h
    have hx : (⇑X : H → H)
        = (⇑(L.symm : H →L[ℂ] H)) ∘ (⇑((L : H →L[ℂ] H) ∘L X)) := by
      funext y
      simp
    rw [hx]
    exact h.clm_comp (L.symm : H →L[ℂ] H)
  · intro h
    exact h.clm_comp (L : H →L[ℂ] H)

omit [CompleteSpace H] in
/-- **Schatten membership is invariant under two-sided multiplication by invertibles.** -/
theorem memSchattenClass_equiv_comp_iff {p : ℝ} (hp : 0 < p) (L : H ≃L[ℂ] H) (X : H →L[ℂ] H) :
    MemSchattenClass p ((L : H →L[ℂ] H) ∘L X) ↔ MemSchattenClass p X := by
  constructor
  · intro h
    have hx : X = (L.symm : H →L[ℂ] H) ∘L ((L : H →L[ℂ] H) ∘L X) := by
      ext y
      simp
    rw [hx]
    exact memSchattenClass_comp_left hp h
  · intro h
    exact memSchattenClass_comp_left hp h

/-- **Trace-class restricted resolvents give a trace-class corner**, even when the Euler metric
crossing itself is noncompact. -/
theorem memSchattenClass_one_sylvester {Q G Rhat Rinf : H →L[ℂ] H}
    (hA : MemSchattenClass 1 (soninOuter Q Rhat))
    (hB : MemSchattenClass 1 (soninInner Q Rinf)) :
    MemSchattenClass 1
      (soninOuter Q Rhat * soninCross Q G - soninCross Q G * soninInner Q Rinf) := by
  have h1 : MemSchattenClass 1 (soninOuter Q Rhat * soninCross Q G) :=
    memSchattenClass_comp_right (by norm_num) hA
  have h2 : MemSchattenClass 1 (soninCross Q G * soninInner Q Rinf) :=
    memSchattenClass_comp_left (by norm_num) hB
  exact MemSchattenClass.one_sub h1 h2

omit [CompleteSpace H] in
/-- **The vanishing criterion.**  The Sonin corner vanishes exactly when the Euler metric crossing
intertwines the two restricted resolvents. -/
theorem sonin_corner_eq_zero_iff {Q G Rhat Rinf : H →L[ℂ] H} :
    soninOuter Q Rhat * soninCross Q G - soninCross Q G * soninInner Q Rinf = 0
      ↔ soninOuter Q Rhat * soninCross Q G = soninCross Q G * soninInner Q Rinf :=
  sub_eq_zero


/-! ## The spectral consequences of a vanishing corner -/

/-- **Item 4.**  A vanishing Sonin corner makes the Euler metric crossing intertwine the whole
continuous functional calculus of the two restricted resolvents, not merely the resolvents
themselves. -/
theorem sonin_cfc_intertwine [Nontrivial (H →L[ℂ] H)] {Q G Rhat Rinf : H →L[ℂ] H}
    (hA : IsSelfAdjoint (soninOuter Q Rhat)) (hB : IsSelfAdjoint (soninInner Q Rinf))
    (hzero : soninOuter Q Rhat * soninCross Q G - soninCross Q G * soninInner Q Rinf = 0)
    {f : ℝ → ℝ} (hf : Continuous f) :
    cfc f (soninOuter Q Rhat) * soninCross Q G
      = soninCross Q G * cfc f (soninInner Q Rinf) :=
  cfc_mul_eq_mul_cfc_of_intertwine hA hB (sub_eq_zero.mp hzero) hf

/-- **Item 5.**  If the two restricted self-adjoint spectra are disjoint, a vanishing corner forces
the Euler metric crossing itself to vanish. -/
theorem soninCross_eq_zero_of_disjoint_spectrum [Nontrivial (H →L[ℂ] H)]
    {Q G Rhat Rinf : H →L[ℂ] H}
    (hA : IsSelfAdjoint (soninOuter Q Rhat)) (hB : IsSelfAdjoint (soninInner Q Rinf))
    (hzero : soninOuter Q Rhat * soninCross Q G - soninCross Q G * soninInner Q Rinf = 0)
    (hdisj : Disjoint (spectrum ℝ (soninOuter Q Rhat)) (spectrum ℝ (soninInner Q Rinf))) :
    soninCross Q G = 0 :=
  eq_zero_of_intertwine_of_disjoint_spectrum hA hB (sub_eq_zero.mp hzero) hdisj

/-- **Item 5, in the form the card states it.**  A nonzero Euler metric crossing and disjoint
restricted spectra force a nonzero corner. -/
theorem sonin_corner_ne_zero_of_disjoint_spectrum [Nontrivial (H →L[ℂ] H)]
    {Q G Rhat Rinf : H →L[ℂ] H}
    (hA : IsSelfAdjoint (soninOuter Q Rhat)) (hB : IsSelfAdjoint (soninInner Q Rinf))
    (hne : soninCross Q G ≠ 0)
    (hdisj : Disjoint (spectrum ℝ (soninOuter Q Rhat)) (spectrum ℝ (soninInner Q Rinf))) :
    soninOuter Q Rhat * soninCross Q G - soninCross Q G * soninInner Q Rinf ≠ 0 := by
  intro hzero
  exact hne (soninCross_eq_zero_of_disjoint_spectrum hA hB hzero hdisj)

end

end RHTower
