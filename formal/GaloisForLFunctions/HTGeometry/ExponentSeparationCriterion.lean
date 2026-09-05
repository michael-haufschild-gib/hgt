import GaloisForLFunctions.HTGeometry.IntegerTranslateJetFullRank

/-!
# When the order form separates the exponents

The full-rank datum for the moving canonical jets rests on one input that is not a theorem:
injectivity of the integer order form on the exponent family.  That input is checkable.

The order of a monomial is `e_{k₀}·(m k₀ + 1) − Σ_{k≠k₀} e_k·V k`.  The companions contribute a
bounded amount, so once the distinguished jet is differentiated far enough — beyond the total
companion contribution over the exponent box — the distinguished coordinate dominates and separation
of the exponents in that one coordinate is inherited by the whole form.

Since the differentiation order `m k₀` is ours to choose, the last hypothesis becomes an explicit
inequality rather than an assumption.
-/

namespace GaloisForLFunctions.HTGeometry

/-- The order of a jet monomial at a translated zero, explicitly. -/
theorem integerBlowUpOrder_integerTranslateJetRate {n : ℕ} (m : Fin n → ℕ) (k₀ : Fin n)
    (V : Fin n → ℕ) (e : Fin n →₀ ℕ) :
    integerBlowUpOrder (integerTranslateJetRate m k₀ V) e
      = (e k₀ : ℤ) * ((m k₀ : ℤ) + 1)
        - ∑ k ∈ Finset.univ.erase k₀, (e k : ℤ) * (V k : ℤ) := by
  classical
  have hdef : integerBlowUpOrder (integerTranslateJetRate m k₀ V) e
      = ∑ k : Fin n, ((e k : ℤ) * integerTranslateJetRate m k₀ V k) := by
    rw [integerBlowUpOrder, Finsupp.sum]
    refine Finset.sum_subset (Finset.subset_univ _) fun k _ hk => ?_
    have hz : e k = 0 := by
      by_contra hne
      exact hk (Finsupp.mem_support_iff.mpr hne)
    rw [hz]
    simp
  have hsplit := Finset.add_sum_erase (Finset.univ : Finset (Fin n))
    (fun k => ((e k : ℤ) * integerTranslateJetRate m k₀ V k)) (Finset.mem_univ k₀)
  have hk₀ : ((e k₀ : ℤ) * integerTranslateJetRate m k₀ V k₀)
      = (e k₀ : ℤ) * ((m k₀ : ℤ) + 1) := by
    simp [integerTranslateJetRate]
  have hrest : ∀ k ∈ Finset.univ.erase k₀,
      ((e k : ℤ) * integerTranslateJetRate m k₀ V k) = -((e k : ℤ) * (V k : ℤ)) := by
    intro k hk
    rw [integerTranslateJetRate]
    simp only [if_neg (Finset.ne_of_mem_erase hk)]
    ring
  rw [hdef, ← hsplit, hk₀, Finset.sum_congr rfl hrest, Finset.sum_neg_distrib]
  ring

/-- **A dominant distinguished rate inherits separation.**  If every exponent is bounded by `E` and
the distinguished jet is differentiated beyond the total companion contribution, then separation in
the distinguished coordinate gives injectivity of the whole order form. -/
theorem injective_integerBlowUpOrder_of_dominant_rate {κ : Type*} {n : ℕ}
    (m : Fin n → ℕ) (k₀ : Fin n) (V : Fin n → ℕ)
    {exponent : κ → (Fin n →₀ ℕ)} (E : ℕ)
    (hE : ∀ a k, exponent a k ≤ E)
    (hbig : (∑ k ∈ Finset.univ.erase k₀, (E : ℤ) * (V k : ℤ)) < (m k₀ : ℤ) + 1)
    (hsep : Function.Injective fun a => exponent a k₀) :
    Function.Injective fun a =>
      integerBlowUpOrder (integerTranslateJetRate m k₀ V) (exponent a) := by
  classical
  intro a b hab
  simp only [integerBlowUpOrder_integerTranslateJetRate] at hab
  set M : ℤ := (m k₀ : ℤ) + 1 with hM
  set B : ℤ := ∑ k ∈ Finset.univ.erase k₀, (E : ℤ) * (V k : ℤ) with hB
  set Sa : ℤ := ∑ k ∈ Finset.univ.erase k₀, ((exponent a k : ℤ) * (V k : ℤ)) with hSa
  set Sb : ℤ := ∑ k ∈ Finset.univ.erase k₀, ((exponent b k : ℤ) * (V k : ℤ)) with hSb
  have hSa0 : 0 ≤ Sa := by
    rw [hSa]
    exact Finset.sum_nonneg fun k _ => by positivity
  have hSb0 : 0 ≤ Sb := by
    rw [hSb]
    exact Finset.sum_nonneg fun k _ => by positivity
  have hSaB : Sa ≤ B := by
    rw [hSa, hB]
    refine Finset.sum_le_sum fun k _ => ?_
    have h1 : ((exponent a k : ℤ)) ≤ (E : ℤ) := by exact_mod_cast hE a k
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  have hSbB : Sb ≤ B := by
    rw [hSb, hB]
    refine Finset.sum_le_sum fun k _ => ?_
    have h1 : ((exponent b k : ℤ)) ≤ (E : ℤ) := by exact_mod_cast hE b k
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  have hMpos : 0 < M := by
    rw [hM]
    positivity
  have hkey : ((exponent a k₀ : ℤ) - (exponent b k₀ : ℤ)) * M = Sa - Sb := by
    linear_combination hab
  refine hsep ?_
  by_contra hne
  have hdiff : ((exponent a k₀ : ℤ)) - ((exponent b k₀ : ℤ)) ≠ 0 := by
    intro h0
    exact hne (Nat.cast_injective (by linarith [h0] : ((exponent a k₀ : ℤ)) = (exponent b k₀ : ℤ)))
  have hone : 1 ≤ |((exponent a k₀ : ℤ)) - ((exponent b k₀ : ℤ))| :=
    Int.one_le_abs (by omega)
  have hlow : M ≤ |Sa - Sb| := by
    rw [← hkey, abs_mul, abs_of_pos hMpos]
    exact le_mul_of_one_le_left hMpos.le hone
  have hhigh : |Sa - Sb| ≤ B := by
    rw [abs_le]
    constructor <;> linarith
  linarith [hlow, hhigh, hbig]


/-- **The full-rank datum for the moving canonical jets, with every hypothesis explicit.**  The
configuration data are: the distinguished shift real and the others strictly above it, the
companions' analytic orders at the sampled points, a bound on the exponents, and a differentiation
order for the distinguished jet exceeding the total companion contribution.  Nothing is assumed
about the family beyond separation of the exponents in the distinguished coordinate. -/
theorem exists_row_packet_upperHalfPlane_movingCanonicalJets
    {κ row : Type*} [Fintype κ] [DecidableEq κ] [Fintype row] {n q : ℕ}
    (θ : BoundedRealSequence) (m : Fin n → ℕ) (σ : Fin n → ℂ) (k₀ : Fin n) (V : Fin n → ℕ)
    (E : ℕ)
    (hshift : ∀ k, k ≠ k₀ → (σ k₀).im < (σ k).im) (hσ0 : (σ k₀).im = 0)
    {Z : Set ℂ} (hZ : Z.Infinite)
    (hzero : ∀ ζ ∈ Z, ∃ p : ℕ, ζ = (movingCanonicalZero θ p : ℂ) - σ k₀)
    (hV : ∀ ζ ∈ Z, ∀ k, k ≠ k₀ →
      analyticOrderAt (fun w => iteratedDeriv (m k) (movingCanonicalLogDerivative θ) (w + σ k)) ζ
        = ((V k : ℕ) : ℕ∞))
    {exponent : κ → (Fin n →₀ ℕ)}
    (hE : ∀ a k, exponent a k ≤ E)
    (hbig : (∑ k ∈ Finset.univ.erase k₀, (E : ℤ) * (V k : ℤ)) < (m k₀ : ℤ) + 1)
    (hsep : Function.Injective fun a => exponent a k₀)
    (f : κ × Fin (q + 1) → row) (hf : Function.Injective f) :
    ∃ z : row → ℂ, (∀ b, 0 < (z b).im) ∧ Function.Injective z ∧
      Function.Injective (expandedDifferentialEvaluationMatrix q n z exponent
        (fun p => iteratedDeriv (m p.2) (movingCanonicalLogDerivative θ) (z p.1 + σ p.2))).mulVec :=
  exists_row_packet_upperHalfPlane_integerTranslateJets (κ := κ) (row := row) (q := q)
    (Z := Z) (exponent := exponent) θ m σ k₀ V hshift hσ0 hZ hzero hV
    (injective_integerBlowUpOrder_of_dominant_rate (κ := κ) m k₀ V E hE hbig hsep) f hf

end GaloisForLFunctions.HTGeometry
