import GaloisForLFunctions.HTGeometry.FiniteAutomorphismOrbitAlgebraicity
import GaloisForLFunctions.HTGeometry.DifferenceGaloisRepresentation

/-!
# Finite difference-Galois groups force algebraicity

The finite-orbit product argument works for any subgroup of base-field automorphisms.  Specializing
to `differenceAut` gives the ordinary Picard--Vessiot finite-group-to-algebraicity bridge.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

local instance : DecidableEq L := Classical.decEq L

/-- A finite stable packet for a subgroup gives algebraicity when subgroup invariants descend. -/
theorem isAlgebraic_of_finite_stable_subgroup_orbit
    (G : Subgroup (L ≃ₐ[K] L)) {x : L} {S : Finset L} (hx : x ∈ S)
    (hstable : ∀ g : G, S.image (g.1 : L → L) = S)
    (hfixed : ∀ y : L, (∀ g : G, g.1 y = y) →
      ∃ k : K, algebraMap K L k = y) :
    IsAlgebraic K x := by
  classical
  let P := finiteOrbitPolynomial S
  have hcoeff : ∀ n, P.coeff n ∈ (algebraMap K L).range := by
    intro n
    apply hfixed
    intro g
    have hmap :
        (finiteOrbitPolynomial S).map g.1.toRingEquiv.toRingHom =
          finiteOrbitPolynomial S := by
      rw [finiteOrbitPolynomial_map, hstable g]
    have hc := congrArg (fun Q : Polynomial L => Q.coeff n) hmap
    change g.1.toRingEquiv.toRingHom (P.coeff n) = P.coeff n
    simpa only [P, Polynomial.coeff_map] using hc
  obtain ⟨q, hq⟩ := exists_map_polynomial_eq_of_coeff_mem_range
    (algebraMap K L) P hcoeff
  have hP0 : P ≠ 0 := (finiteOrbitPolynomial_monic S).ne_zero
  have hq0 : q ≠ 0 := by
    intro hzero
    rw [hzero, Polynomial.map_zero] at hq
    exact hP0 hq.symm
  refine ⟨q, hq0, ?_⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, hq]
  exact finiteOrbitPolynomial_eval_eq_zero hx

/-- A finite automorphism subgroup forces algebraicity when its invariant field is the base. -/
theorem isAlgebraic_of_finite_automorphismSubgroup
    (G : Subgroup (L ≃ₐ[K] L)) [Finite G] {x : L}
    (hfixed : ∀ y : L, (∀ g : G, g.1 y = y) →
      ∃ k : K, algebraMap K L k = y) :
    IsAlgebraic K x := by
  classical
  let O : Set L := Set.range (fun g : G => g.1 x)
  have hfinite : O.Finite := Set.finite_range _
  let S := hfinite.toFinset
  have hx : x ∈ S := by
    have hxO : x ∈ O := ⟨1, rfl⟩
    simpa only [S, Set.Finite.mem_toFinset] using hxO
  have hstable : ∀ g : G, S.image (g.1 : L → L) = S := by
    intro g
    ext y
    constructor
    · intro hy
      obtain ⟨z, hz, hzy⟩ := Finset.mem_image.mp hy
      have hzO : z ∈ O := by
        simpa only [S, Set.Finite.mem_toFinset] using hz
      obtain ⟨h, rfl⟩ := hzO
      have hyO : y ∈ O := by
        refine ⟨g * h, ?_⟩
        change g.1 (h.1 x) = y
        exact hzy
      simpa only [S, Set.Finite.mem_toFinset] using hyO
    · intro hy
      have hyO : y ∈ O := by
        simpa only [S, Set.Finite.mem_toFinset] using hy
      obtain ⟨h, rfl⟩ := hyO
      refine Finset.mem_image.mpr
        ⟨g.1.symm (h.1 x), ?_, g.1.apply_symm_apply (h.1 x)⟩
      have hzO : g.1.symm (h.1 x) ∈ O := by
        refine ⟨g⁻¹ * h, ?_⟩
        change g.1.symm (h.1 x) = g.1.symm (h.1 x)
        rfl
      simpa only [S, Set.Finite.mem_toFinset] using hzO
  exact isAlgebraic_of_finite_stable_subgroup_orbit G hx hstable hfixed

/-- Finite ordinary difference-Galois group plus fixed-field descent forces algebraicity. -/
theorem isAlgebraic_of_finite_differenceAut
    {σL : L ≃+* L} [Finite (differenceAut (K := K) σL)] {x : L}
    (hfixed : ∀ y : L, (∀ g : differenceAut (K := K) σL, g.1 y = y) →
      ∃ k : K, algebraMap K L k = y) :
    IsAlgebraic K x :=
  isAlgebraic_of_finite_automorphismSubgroup (differenceAut σL) hfixed

/-- A transcendental carrier rules out a finite ordinary difference-Galois group after fixed-field
descent. -/
theorem not_finite_differenceAut_of_transcendental
    {σL : L ≃+* L} {x : L} (hx : Transcendental K x)
    (hfixed : ∀ y : L, (∀ g : differenceAut (K := K) σL, g.1 y = y) →
      ∃ k : K, algebraMap K L k = y) :
    ¬ Finite (differenceAut (K := K) σL) := by
  intro hfinite
  letI : Finite (differenceAut (K := K) σL) := hfinite
  exact hx (isAlgebraic_of_finite_differenceAut hfixed)

/-- An injective map with finite range has finite domain. -/
theorem finite_of_finite_range_of_injective
    {α β : Type*} {f : α → β} (hfinite : (Set.range f).Finite)
    (hinj : Function.Injective f) :
    Finite α := by
  letI : Fintype (Set.range f) := hfinite.fintype
  exact Finite.of_injective
    (fun x : α => (⟨f x, ⟨x, rfl⟩⟩ : Set.range f))
    (fun _ _ h => hinj (Subtype.ext_iff.mp h))

/-- Finite image of the faithful ordinary Galois representation forces the difference
automorphism group to be finite. -/
theorem finite_differenceAut_of_finite_galoisRepresentation_range
    {n : ℕ} (σL : L ≃+* L) (B : Matrix (Fin n) (Fin n) K)
    (Y : Matrix (Fin n) (Fin n) L) [Invertible Y]
    (hY : Y.map (σL : L → L) = (B.map (algebraMap K L)) * Y)
    (hnc : ∀ y : L, σL y = y → ∃ k : K, y = algebraMap K L k)
    (u : L) (hu : Y.det * u = 1)
    (htop : Algebra.adjoin K
      (Set.range (fun p : Fin n × Fin n => Y p.1 p.2) ∪ {u}) = ⊤)
    (hfinite : (Set.range (galoisRepresentation σL B Y hY hnc)).Finite) :
    Finite (differenceAut (K := K) σL) :=
  finite_of_finite_range_of_injective hfinite
    (galoisRepresentation_injective σL B Y hY hnc u hu htop)

/-- A transcendental PV carrier forces the faithful ordinary Galois representation to have
infinite image once both fixed-field descents are available. -/
theorem galoisRepresentation_range_infinite_of_transcendental
    {n : ℕ} (σL : L ≃+* L) (B : Matrix (Fin n) (Fin n) K)
    (Y : Matrix (Fin n) (Fin n) L) [Invertible Y]
    (hY : Y.map (σL : L → L) = (B.map (algebraMap K L)) * Y)
    (hnc : ∀ y : L, σL y = y → ∃ k : K, y = algebraMap K L k)
    (u : L) (hu : Y.det * u = 1)
    (htop : Algebra.adjoin K
      (Set.range (fun p : Fin n × Fin n => Y p.1 p.2) ∪ {u}) = ⊤)
    {x : L} (hx : Transcendental K x)
    (hfixed : ∀ y : L, (∀ g : differenceAut (K := K) σL, g.1 y = y) →
      ∃ k : K, algebraMap K L k = y) :
    (Set.range (galoisRepresentation σL B Y hY hnc)).Infinite := by
  intro hfinite
  letI : Finite (differenceAut (K := K) σL) :=
    finite_differenceAut_of_finite_galoisRepresentation_range
      σL B Y hY hnc u hu htop hfinite
  exact hx (isAlgebraic_of_finite_differenceAut hfixed)

end

end GaloisForLFunctions.HTGeometry
