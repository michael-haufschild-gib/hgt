import GaloisForLFunctions.HTGeometry.PolynomialRecessionLocallyUniform
import GaloisForLFunctions.HTGeometry.GammaPhaseCompletion
import GaloisForLFunctions.HTGeometry.ConstantProjectiveBoundaryWitness

/-!
# The polynomial class realizes the projective-boundary interface

Every finite nonzero tuple of polynomial functions, translated up the imaginary axis and normalized
by `(iT)^{-d}` with `d` the common degree bound, converges locally uniformly to the constant
polynomial named by the degree-`d` coefficients, and that limit vector is nonzero.  So the
polynomial class satisfies `HasPolynomialFunctionalProjectiveBoundary` with genuinely
degree-carrying data, not merely constants.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators

noncomputable section

/-- The polynomial functions, as a coefficient class. -/
def polynomialFunctionClass : Set (ℂ → ℂ) := {f | ∃ p : Polynomial ℂ, f = fun z => p.eval z}

theorem TendstoLocallyUniformly.comp_tendsto {α β ι κ : Type*} [TopologicalSpace α]
    [UniformSpace β] {F : ι → α → β} {f : α → β} {p : Filter ι} {q : Filter κ} {g : κ → ι}
    (h : TendstoLocallyUniformly F f p) (hg : Tendsto g q p) :
    TendstoLocallyUniformly (fun k => F (g k)) f q := by
  intro v hv x
  obtain ⟨t, ht, hev⟩ := h v hv x
  exact ⟨t, ht, hg.eventually hev⟩

/-- The common degree bound of a finite tuple carries a nonzero coefficient. -/
theorem exists_coeff_sup_natDegree_ne_zero {r : ℕ} (p : Fin r → Polynomial ℂ)
    (hp : ∃ j, p j ≠ 0) :
    ∃ j, (p j).coeff (Finset.univ.sup fun j => (p j).natDegree) ≠ 0 := by
  classical
  obtain ⟨j0, hj0⟩ := hp
  set d := Finset.univ.sup (fun j => (p j).natDegree) with hd
  obtain ⟨jmax, -, hjmax⟩ :=
    Finset.exists_mem_eq_sup Finset.univ ⟨j0, Finset.mem_univ j0⟩ (fun j => (p j).natDegree)
  by_cases hj : p jmax = 0
  · have hd0 : d = 0 := by rw [hd, hjmax, hj, Polynomial.natDegree_zero]
    have hnd0 : (p j0).natDegree = 0 :=
      Nat.le_zero.mp (hd0 ▸ Finset.le_sup (f := fun j => (p j).natDegree) (Finset.mem_univ j0))
    refine ⟨j0, ?_⟩
    rw [hd0]
    have hlc : (p j0).coeff ((p j0).natDegree) ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hj0
    rwa [hnd0] at hlc
  · refine ⟨jmax, ?_⟩
    have hdeq : d = (p jmax).natDegree := hd.trans hjmax
    rw [hdeq]
    exact Polynomial.leadingCoeff_ne_zero.mpr hj

/-- **The polynomial class satisfies the projective-boundary interface.** -/
theorem hasPolynomialFunctionalProjectiveBoundary_polynomialFunctionClass :
    HasPolynomialFunctionalProjectiveBoundary polynomialFunctionClass := by
  classical
  intro r a haK ha S hS
  choose p hp using fun j => haK j
  obtain ⟨j0, hj0⟩ := ha
  have hp0 : ∃ j, p j ≠ 0 := by
    refine ⟨j0, ?_⟩
    intro hzero
    apply hj0
    rw [hp j0, hzero]
    funext z
    simp
  set d := Finset.univ.sup (fun j => (p j).natDegree) with hd
  obtain ⟨j1, hj1⟩ := exists_coeff_sup_natDegree_ne_zero p hp0
  refine ⟨id, strictMono_id, fun k _ => ((Complex.I * (S k : ℂ)) ^ d)⁻¹,
    fun j => Polynomial.C ((p j).coeff d), ⟨j1, ?_⟩, ?_⟩
  · intro hzero
    apply hj1
    have := congrArg (fun t : Polynomial ℂ => t.coeff 0) hzero
    simpa using this
  · intro j
    have hdeg : (p j).natDegree ≤ d :=
      Finset.le_sup (f := fun j => (p j).natDegree) (Finset.mem_univ j)
    have hbase := TendstoLocallyUniformly.comp_tendsto
      (poly_scaled_translate_tendstoLocallyUniformly (p j) hdeg) hS
    have hfun : (fun (k : ℕ) (z : ℂ) =>
        ((Complex.I * (S k : ℂ)) ^ d)⁻¹ * a j (z + Complex.I * (S k : ℂ)))
        = fun (k : ℕ) (z : ℂ) =>
          (p j).eval (z + Complex.I * (S k : ℂ)) / (Complex.I * (S k : ℂ)) ^ d := by
      funext k z
      rw [hp j, div_eq_mul_inv, mul_comm]
    have hlim : (fun z : ℂ => (Polynomial.C ((p j).coeff d)).eval z)
        = fun _ : ℂ => (p j).coeff d := by
      funext z
      simp
    show TendstoLocallyUniformly
      (fun (k : ℕ) (z : ℂ) =>
        ((Complex.I * (S k : ℂ)) ^ d)⁻¹ * a j (z + Complex.I * (S k : ℂ)))
      (fun z : ℂ => (Polynomial.C ((p j).coeff d)).eval z) atTop
    rw [hfun, hlim]
    exact hbase

/-- **The projective-boundary interface is antitone in the coefficient class.**  A smaller class has
fewer tuples to test, so it inherits the property.  Consequently any class contained in the
polynomial functions — the constants among them — realizes the interface. -/
theorem HasPolynomialFunctionalProjectiveBoundary.mono {K K' : Set (ℂ → ℂ)} (hKK' : K' ⊆ K)
    (h : HasPolynomialFunctionalProjectiveBoundary K) :
    HasPolynomialFunctionalProjectiveBoundary K' := by
  intro r a haK ha S hS
  exact h a (fun j => hKK' (haK j)) ha S hS

theorem constantFunctionClass_subset_polynomialFunctionClass :
    constantFunctionClass ⊆ polynomialFunctionClass := by
  rintro f ⟨c, rfl⟩
  exact ⟨Polynomial.C c, by funext z; simp⟩


/-- **A common nowhere-zero factor can be absorbed into the normalization.**  If every member of a
class is a fixed nonvanishing `g` times a member of a class with the projective boundary property,
the product class has it too: divide the normalization by the translated `g`.  This is the formal
content of the paper step "restoring the cleared denominator and the common gcd as one meromorphic
functional normalization". -/
theorem HasPolynomialFunctionalProjectiveBoundary.mul_left {K : Set (ℂ → ℂ)} {g : ℂ → ℂ}
    (hg : ∀ z, g z ≠ 0) (h : HasPolynomialFunctionalProjectiveBoundary K) :
    HasPolynomialFunctionalProjectiveBoundary {u : ℂ → ℂ | ∃ f ∈ K, u = fun z => g z * f z} := by
  intro r a haK ha S hS
  choose f hfK hfa using fun j => haK j
  have hf : ∃ j, f j ≠ 0 := by
    obtain ⟨j0, hj0⟩ := ha
    refine ⟨j0, ?_⟩
    intro hzero
    apply hj0
    rw [hfa j0, hzero]
    funext z
    simp
  obtain ⟨phi, hphi, normalization, limit, hne, hconv⟩ := h f hfK hf S hS
  refine ⟨phi, hphi,
    fun k z => normalization k z * (g (z + Complex.I * (S (phi k) : ℂ)))⁻¹, limit, hne, ?_⟩
  intro j
  have hrw : (fun (k : ℕ) (z : ℂ) =>
      normalization k z * (g (z + Complex.I * (S (phi k) : ℂ)))⁻¹ *
        a j (z + Complex.I * (S (phi k) : ℂ)))
      = fun (k : ℕ) (z : ℂ) =>
        normalization k z * f j (z + Complex.I * (S (phi k) : ℂ)) := by
    funext k z
    have hgz : g (z + Complex.I * (S (phi k) : ℂ)) ≠ 0 := hg _
    rw [hfa j]
    field_simp
  rw [hrw]
  exact hconv j


/-- **The entry point for the Gamma-ratio class.**  For any nowhere-zero `g`, the class of
`g`-multiples of polynomial functions realizes the projective-boundary interface.  Combined with
`HasPolynomialFunctionalProjectiveBoundary.mono`, it suffices to exhibit the Gamma-ratio class
inside `g · ℂ[z]` for one nowhere-zero `g`. -/
theorem hasPolynomialFunctionalProjectiveBoundary_mul_polynomialFunctionClass
    {g : ℂ → ℂ} (hg : ∀ z, g z ≠ 0) :
    HasPolynomialFunctionalProjectiveBoundary
      {u : ℂ → ℂ | ∃ f ∈ polynomialFunctionClass, u = fun z => g z * f z} :=
  HasPolynomialFunctionalProjectiveBoundary.mul_left hg
    hasPolynomialFunctionalProjectiveBoundary_polynomialFunctionClass

/-- Every subclass of `g · ℂ[z]` inherits the interface. -/
theorem hasPolynomialFunctionalProjectiveBoundary_of_subset_mul_polynomial
    {g : ℂ → ℂ} (hg : ∀ z, g z ≠ 0) {K : Set (ℂ → ℂ)}
    (hK : K ⊆ {u : ℂ → ℂ | ∃ f ∈ polynomialFunctionClass, u = fun z => g z * f z}) :
    HasPolynomialFunctionalProjectiveBoundary K :=
  HasPolynomialFunctionalProjectiveBoundary.mono hK
    (hasPolynomialFunctionalProjectiveBoundary_mul_polynomialFunctionClass hg)


end

end GaloisForLFunctions.HTGeometry
