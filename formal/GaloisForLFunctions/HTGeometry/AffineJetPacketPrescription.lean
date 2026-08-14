import GaloisForLFunctions.HTGeometry.AffineJetVanishingTransfer
import GaloisForLFunctions.HTGeometry.MultivariateJetCompositionLaw

/-!
# Prescribing an affine jet packet

Composition with an affine automorphism is a substitution on multivariable polynomials, so the
polynomial sources are stable under every frame.  Combining that with one-point Taylor data and the
Hermite jet packet at the distinct image points produces a single polynomial source realizing an
arbitrary finite family of mixed jets of all its affine pullbacks: the analytic surjectivity that
the affine jet-packet collision law needs.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

/-- The `i`-th coordinate of an affine automorphism, as a degree-one polynomial. -/
def affineCoordPolynomial {d : ℕ} (e : (Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ)) (i : Fin d) :
    MvPolynomial (Fin d) ℂ :=
  C (e 0 i) +
    ∑ j : Fin d, C (e.toContinuousAffineMap.contLinear (Pi.single j 1) i) * X j

theorem pi_single_eq_smul {d : ℕ} (z : Fin d → ℂ) (j : Fin d) :
    Pi.single j (z j) = z j • (Pi.single j 1 : Fin d → ℂ) := by
  classical
  funext k
  by_cases h : k = j
  · subst h
    simp
  · simp [h]

theorem contLinear_apply_eq_sum {d : ℕ} (e : (Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ))
    (z : Fin d → ℂ) (i : Fin d) :
    e.toContinuousAffineMap.contLinear z i =
      ∑ j : Fin d, z j * e.toContinuousAffineMap.contLinear (Pi.single j 1) i := by
  classical
  have hz : z = ∑ j : Fin d, Pi.single j (z j) := (Finset.univ_sum_single z).symm
  calc e.toContinuousAffineMap.contLinear z i
      = e.toContinuousAffineMap.contLinear (∑ j : Fin d, Pi.single j (z j)) i := by rw [← hz]
    _ = (∑ j : Fin d, e.toContinuousAffineMap.contLinear (Pi.single j (z j))) i := by
        rw [map_sum]
    _ = ∑ j : Fin d, e.toContinuousAffineMap.contLinear (Pi.single j (z j)) i := by
        simp
    _ = ∑ j : Fin d, z j * e.toContinuousAffineMap.contLinear (Pi.single j 1) i := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [pi_single_eq_smul, map_smul]
        simp [smul_eq_mul]

theorem apply_eq_contLinear_add {d : ℕ} (e : (Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ))
    (z : Fin d → ℂ) : e z = e.toContinuousAffineMap.contLinear z + e 0 := by
  have := e.toContinuousAffineMap.toAffineMap.map_vadd (0 : Fin d → ℂ) z
  simpa using this

@[simp] theorem eval_affineCoordPolynomial {d : ℕ} (e : (Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ))
    (i : Fin d) (z : Fin d → ℂ) :
    eval z (affineCoordPolynomial e i) = e z i := by
  rw [affineCoordPolynomial]
  rw [apply_eq_contLinear_add e z]
  simp only [Pi.add_apply, map_add, map_sum, eval_C, eval_mul, eval_X]
  rw [contLinear_apply_eq_sum e z i]
  have hcomm : ∀ j : Fin d,
      e.toContinuousAffineMap.contLinear (Pi.single j 1) i * z j =
        z j * e.toContinuousAffineMap.contLinear (Pi.single j 1) i := fun j => mul_comm _ _
  simp_rw [hcomm]
  ring

/-- Composition with an affine automorphism as a substitution on polynomials. -/
def mvPolynomialAffineSubst {d : ℕ} (e : (Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ))
    (Q : MvPolynomial (Fin d) ℂ) : MvPolynomial (Fin d) ℂ :=
  aeval (affineCoordPolynomial e) Q

@[simp] theorem eval_mvPolynomialAffineSubst {d : ℕ} (e : (Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ))
    (Q : MvPolynomial (Fin d) ℂ) (z : Fin d → ℂ) :
    eval z (mvPolynomialAffineSubst e Q) = eval (e z) Q := by
  have h := MvPolynomial.comp_aeval (R := ℂ) (B := ℂ)
    (f := affineCoordPolynomial e) (φ := (aeval z : MvPolynomial (Fin d) ℂ →ₐ[ℂ] ℂ))
  have h2 := congrArg (fun φ : MvPolynomial (Fin d) ℂ →ₐ[ℂ] ℂ => φ Q) h
  simp only [mvPolynomialAffineSubst]
  simpa [MvPolynomial.aeval_eq_eval] using h2

/-- The polynomial sources are stable under affine pullback. -/
theorem multivariateEntireAffinePullback_mvPolynomial {d : ℕ}
    (e : (Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ)) (Q : MvPolynomial (Fin d) ℂ) :
    multivariateEntireAffinePullback e (mvPolynomialMultivariateEntire Q) =
      mvPolynomialMultivariateEntire (mvPolynomialAffineSubst e Q) := by
  apply Subtype.ext
  ext z
  simp [multivariateEntireAffinePullback, mvPolynomialMultivariateEntire]

/-- **One affine frame prescribes its own jet packet.**  For any point, order and jet data there is
a polynomial source whose mixed pullback jets along the frame are exactly the data. -/
theorem exists_mvPolynomial_affineMultiIndexJetEvalCLM_eq
    {d : ℕ} (e : (Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ)) (x : Fin d → ℂ) (m : ℕ)
    (c : (Fin d →₀ ℕ) → ℂ) :
    ∃ Q : MvPolynomial (Fin d) ℂ, ∀ a : Fin d →₀ ℕ, Finsupp.degree a < m →
      affineMultiIndexJetEvalCLM e x a (mvPolynomialMultivariateEntire Q) = c a := by
  obtain ⟨H, hH⟩ := exists_mvPolynomial_multiIndexJetEvalCLM_eq_arbitrary
    (I := Unit) (fun _ => x) (fun _ _ _ => rfl) (fun _ => m) (fun _ => c)
  refine ⟨mvPolynomialAffineSubst e.symm H, fun a ha => ?_⟩
  rw [affineMultiIndexJetEvalCLM_apply, ← multivariateEntireAffinePullback_mvPolynomial]
  have hcomp : multivariateEntireAffinePullback e
      (multivariateEntireAffinePullback e.symm (mvPolynomialMultivariateEntire H)) =
      mvPolynomialMultivariateEntire H := by
    apply Subtype.ext
    ext z
    simp [multivariateEntireAffinePullback]
  rw [hcomp]
  exact hH () a ha

/-- **Affine jet packet surjectivity.**  If the image points of the packet are pairwise distinct,
one polynomial source realizes arbitrary mixed jets of every affine pullback at every packet
point. -/
theorem exists_mvPolynomial_affine_packet_prescribed
    {d : ℕ} {I : Type*} [Finite I]
    (e : I → ((Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ))) (x : I → (Fin d → ℂ))
    (hdist : Function.Injective fun i => e i (x i))
    (m : I → ℕ) (c : I → (Fin d →₀ ℕ) → ℂ) :
    ∃ P : MvPolynomial (Fin d) ℂ, ∀ (i : I) (a : Fin d →₀ ℕ), Finsupp.degree a < m i →
      affineMultiIndexJetEvalCLM (e i) (x i) a (mvPolynomialMultivariateEntire P) = c i a := by
  classical
  choose Q hQ using fun i : I =>
    exists_mvPolynomial_affineMultiIndexJetEvalCLM_eq (e i) (x i) (m i) (c i)
  obtain ⟨P, hP⟩ := exists_mvPolynomial_multiIndexJetEvalCLM_eq_arbitrary
    (fun i => e i (x i)) hdist m
    (fun i a => multiIndexJetEvalCLM (e i (x i)) a (mvPolynomialMultivariateEntire (Q i)))
  refine ⟨P, fun i a ha => ?_⟩
  have hjet : ∀ n < m i, ∀ word : Fin n → Fin d,
      orderedPartialJetEvalCLM (e i (x i)) word (mvPolynomialMultivariateEntire P) =
        orderedPartialJetEvalCLM (e i (x i)) word (mvPolynomialMultivariateEntire (Q i)) := by
    intro n hn word
    have hdeg : Finsupp.degree (wordMultiplicity word) < m i := by
      rw [degree_wordMultiplicity]; exact hn
    have hPword := hP i (wordMultiplicity word) hdeg
    rw [orderedPartialJetEvalCLM_mvPolynomial_eq_centered_coeff,
      orderedPartialJetEvalCLM_mvPolynomial_eq_centered_coeff]
    rw [multiIndexJetEvalCLM_mvPolynomial_eq_centered_coeff,
      multiIndexJetEvalCLM_mvPolynomial_eq_centered_coeff] at hPword
    exact hPword
  rw [affineMultiIndexJetEvalCLM_congr_of_orderedPartialJetEvalCLM_eq (e i) (x i) (m i)
    (mvPolynomialMultivariateEntire P) (mvPolynomialMultivariateEntire (Q i)) hjet a ha]
  exact hQ i a ha

end

end GaloisForLFunctions.HTGeometry
