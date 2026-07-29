import GaloisForLFunctions.HTGeometry.StanleyReisnerFacetIdeal

/-!
# Vertex coordinates and the general nonface relation in a Stanley–Reisner ring

For an arbitrary finite complex, presented by its facet family, the Stanley–Reisner ring is the
quotient of the polynomial ring by the nonface monomial ideal.  Its vertex coordinates are the
images of the variables.  The single relation that defines every Stanley–Reisner ring — uniformly
over all finite complexes — is that a product of two distinct vertex coordinates vanishes exactly
when their pair is a nonface.

This is the general form of the concrete nonface relations proved for the discrete, nodal, and
single-edge complexes (`isolatedBoundaryX_mul_eq_zero`, `nodalBoundaryX_mul_Y`,
`singleEdgeX_mul_isoX_eq_zero`), stated once for every finite complex.  It is the foundation for a
uniform Koszul-cohomology / Hochster treatment across arbitrary complexes rather than one concrete
model at a time.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

variable {R α : Type*} [CommRing R] [DecidableEq α]

/-- The Stanley–Reisner ring of a finite facet family: the quotient of the polynomial ring by the
nonface monomial ideal. -/
abbrev stanleyReisnerRing (R : Type*) [CommRing R] (facets : Finset (Finset α)) : Type _ :=
  MvPolynomial α R ⧸ stanleyReisnerIdeal R facets

/-- The vertex coordinate `x_v` in the Stanley–Reisner ring, the image of the variable `X v`. -/
def srVertexX (R : Type*) [CommRing R] (facets : Finset (Finset α)) (v : α) :
    stanleyReisnerRing R facets :=
  Ideal.Quotient.mk (stanleyReisnerIdeal R facets) (X v)

/-- The support of the squarefree exponent of a two-variable product is the pair. -/
theorem support_single_add_single {u v : α} (huv : u ≠ v) :
    (Finsupp.single u (1 : ℕ) + Finsupp.single v 1).support = {u, v} := by
  rw [Finsupp.support_add_eq (by simp [huv])]
  simp [Finset.singleton_union]

/-- **General nonface relation.**  In the Stanley–Reisner ring of any finite complex, the product of
two distinct vertex coordinates vanishes exactly when their pair is a nonface.  This is the single
defining relation of every Stanley–Reisner ring, uniform over all finite complexes. -/
theorem srVertexX_mul_eq_zero_of_not_isFace (facets : Finset (Finset α)) {u v : α} (huv : u ≠ v)
    (hnf : ¬ IsFaceOf (↑facets : Set (Finset α)) {u, v}) :
    srVertexX R facets u * srVertexX R facets v = 0 := by
  rw [srVertexX, srVertexX, ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
    mem_stanleyReisnerIdeal_iff]
  intro d hd
  rw [show (X u * X v : MvPolynomial α R)
        = monomial (Finsupp.single u 1 + Finsupp.single v 1) 1 by
      rw [MvPolynomial.X, MvPolynomial.X, MvPolynomial.monomial_mul]; simp,
    MvPolynomial.mem_support_iff, MvPolynomial.coeff_monomial] at hd
  by_cases hde : (Finsupp.single u 1 + Finsupp.single v 1) = d
  · rw [← hde, support_single_add_single huv]; exact hnf
  · rw [if_neg hde] at hd; exact absurd rfl hd

/-- **General Stanley–Reisner relation.**  In the Stanley–Reisner ring of any finite complex, the
product of the vertex coordinates over any nonface vanishes.  This is the full defining relation of
every Stanley–Reisner ring — the arbitrary-cardinality generalization of the pairwise
`srVertexX_mul_eq_zero_of_not_isFace`. -/
theorem srProd_eq_zero_of_not_isFace (facets : Finset (Finset α)) {J : Finset α}
    (hnf : ¬ IsFaceOf (↑facets : Set (Finset α)) J) :
    ∏ v ∈ J, srVertexX R facets v = 0 := by
  have hmk : (∏ v ∈ J, srVertexX R facets v)
      = Ideal.Quotient.mk (stanleyReisnerIdeal R facets) (∏ v ∈ J, X v) := by
    rw [map_prod]; rfl
  rw [hmk, Ideal.Quotient.eq_zero_iff_mem,
    GaloisForLFunctions.VeroneseIdeal.prod_X_eq_monomial, mem_stanleyReisnerIdeal_iff]
  intro d hd
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_monomial] at hd
  by_cases hde : (∑ j ∈ J, Finsupp.single j 1) = d
  · rw [← hde, GaloisForLFunctions.VeroneseIdeal.support_sum_single]
    exact hnf
  · rw [if_neg hde] at hd; exact absurd rfl hd

/-- **Degree-one coefficient vanishes on the ideal.**  When the singleton `{w}` is a face, the
`x_w`-coefficient reader annihilates the whole Stanley–Reisner ideal: every nonface monomial has
degree at least two, so it contributes nothing to the degree-one coefficient. -/
theorem coeff_single_eq_zero_of_mem_stanleyReisnerIdeal (facets : Finset (Finset α)) {w : α}
    (hw : IsFaceOf (↑facets : Set (Finset α)) {w})
    {P : MvPolynomial α R} (hP : P ∈ stanleyReisnerIdeal R facets) :
    MvPolynomial.coeff (Finsupp.single w 1) P = 0 := by
  by_contra hne
  rw [mem_stanleyReisnerIdeal_iff] at hP
  refine hP _ (MvPolynomial.mem_support_iff.mpr hne) ?_
  rw [show (Finsupp.single w (1 : ℕ)).support = {w} by simp]
  exact hw

/-- The base-to-component reduced-`H⁰` detector for a present vertex `w`: the `x_w`-coefficient
reader, descended to the Stanley–Reisner ring.  It is well-defined on the quotient because the
degree-one coefficient sees nothing in the nonface ideal. -/
noncomputable def srH0Detector (R : Type*) [CommRing R] (facets : Finset (Finset α)) (w : α)
    (hw : IsFaceOf (↑facets : Set (Finset α)) {w}) :
    stanleyReisnerRing R facets →ₗ[R] R :=
  Submodule.liftQ ((stanleyReisnerIdeal R facets).restrictScalars R)
    (MvPolynomial.lcoeff R (Finsupp.single w 1))
    (by
      intro P hP
      rw [Submodule.restrictScalars_mem] at hP
      rw [LinearMap.mem_ker, MvPolynomial.lcoeff_apply]
      exact coeff_single_eq_zero_of_mem_stanleyReisnerIdeal facets hw hP)

@[simp]
theorem srH0Detector_mk (facets : Finset (Finset α)) (w : α)
    (hw : IsFaceOf (↑facets : Set (Finset α)) {w}) (P : MvPolynomial α R) :
    srH0Detector R facets w hw (Ideal.Quotient.mk (stanleyReisnerIdeal R facets) P)
      = MvPolynomial.coeff (Finsupp.single w 1) P := rfl

/-- **Kronecker duality.**  The detector for vertex `w` reads off the vertex coordinate `x_v` as the
Kronecker delta `δ_{wv}`. -/
@[simp]
theorem srH0Detector_srVertexX (facets : Finset (Finset α)) {w v : α}
    (hw : IsFaceOf (↑facets : Set (Finset α)) {w}) :
    srH0Detector R facets w hw (srVertexX R facets v) = if w = v then 1 else 0 := by
  rw [srVertexX, srH0Detector_mk, MvPolynomial.coeff_X]
  simp only [Finsupp.single_eq_single_iff]
  by_cases h : w = v <;> simp [h, eq_comm]

/-- **Constant coefficient vanishes on the ideal.**  When the empty set is a face (equivalently the
facet family is nonempty), the constant-term reader annihilates the Stanley–Reisner ideal: every
nonface is nonempty, so its monomial has positive degree. -/
theorem coeff_zero_eq_zero_of_mem_stanleyReisnerIdeal (facets : Finset (Finset α))
    (hE : IsFaceOf (↑facets : Set (Finset α)) ∅)
    {P : MvPolynomial α R} (hP : P ∈ stanleyReisnerIdeal R facets) :
    MvPolynomial.coeff 0 P = 0 := by
  by_contra hne
  rw [mem_stanleyReisnerIdeal_iff] at hP
  have hnf := hP _ (MvPolynomial.mem_support_iff.mpr hne)
  rw [Finsupp.support_zero] at hnf
  exact hnf hE

/-- The descended constant-term functional on the Stanley–Reisner ring, the degree-zero
coefficient reader. -/
noncomputable def srConstTerm (R : Type*) [CommRing R] (facets : Finset (Finset α))
    (hE : IsFaceOf (↑facets : Set (Finset α)) ∅) : stanleyReisnerRing R facets →ₗ[R] R :=
  Submodule.liftQ ((stanleyReisnerIdeal R facets).restrictScalars R)
    (MvPolynomial.lcoeff R 0)
    (by
      intro P hP
      rw [Submodule.restrictScalars_mem] at hP
      rw [LinearMap.mem_ker, MvPolynomial.lcoeff_apply]
      exact coeff_zero_eq_zero_of_mem_stanleyReisnerIdeal facets hE hP)

@[simp]
theorem srConstTerm_mk (facets : Finset (Finset α)) (hE : IsFaceOf (↑facets : Set (Finset α)) ∅)
    (P : MvPolynomial α R) :
    srConstTerm R facets hE (Ideal.Quotient.mk (stanleyReisnerIdeal R facets) P)
      = MvPolynomial.coeff 0 P := rfl

/-- **Product-detector rule.**  Multiplying by the vertex coordinate `x_j` shifts the degree-zero
part into degree one: the `w`-detector of `r · x_j` is the constant term of `r` when `w = j`, and
zero otherwise.  This is the algebraic heart of the reduced-`H⁰` boundary cancellation. -/
theorem srH0Detector_mul_srVertexX (facets : Finset (Finset α))
    (hE : IsFaceOf (↑facets : Set (Finset α)) ∅) {w j : α}
    (hw : IsFaceOf (↑facets : Set (Finset α)) {w}) (r : stanleyReisnerRing R facets) :
    srH0Detector R facets w hw (r * srVertexX R facets j)
      = if w = j then srConstTerm R facets hE r else 0 := by
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective r
  rw [srVertexX, ← map_mul, srH0Detector_mk, srConstTerm_mk, MvPolynomial.coeff_mul_X',
    show (Finsupp.single w (1 : ℕ)).support = {w} by simp]
  simp only [Finset.mem_singleton]
  by_cases h : j = w
  · subst h; simp
  · rw [if_neg h, if_neg (fun hc => h hc.symm)]

/-- **Coefficient at a face support vanishes on the ideal.**  A monomial-coefficient reader
annihilates the Stanley–Reisner ideal whenever the monomial's support is a face — the general form
behind the degree-zero, degree-one, and degree-two coefficient detectors (a supported monomial of an
ideal element always has nonface support). -/
theorem coeff_eq_zero_of_isFace_support (facets : Finset (Finset α)) {e : α →₀ ℕ}
    (he : IsFaceOf (↑facets : Set (Finset α)) e.support)
    {P : MvPolynomial α R} (hP : P ∈ stanleyReisnerIdeal R facets) :
    MvPolynomial.coeff e P = 0 := by
  by_contra hne
  rw [mem_stanleyReisnerIdeal_iff] at hP
  exact hP _ (MvPolynomial.mem_support_iff.mpr hne) he

/-- The degree-two (pair) detector: the `x_u x_v`-coefficient reader descended to the Stanley–Reisner
ring, well-defined whenever `{u,v}` is a face. -/
noncomputable def srPairDetector (R : Type*) [CommRing R] (facets : Finset (Finset α)) (u v : α)
    (huv : u ≠ v) (hf : IsFaceOf (↑facets : Set (Finset α)) {u, v}) :
    stanleyReisnerRing R facets →ₗ[R] R :=
  Submodule.liftQ ((stanleyReisnerIdeal R facets).restrictScalars R)
    (MvPolynomial.lcoeff R (Finsupp.single u 1 + Finsupp.single v 1))
    (by
      intro P hP
      rw [Submodule.restrictScalars_mem] at hP
      rw [LinearMap.mem_ker, MvPolynomial.lcoeff_apply]
      refine coeff_eq_zero_of_isFace_support facets ?_ hP
      rw [support_single_add_single huv]; exact hf)

@[simp]
theorem srPairDetector_mk (facets : Finset (Finset α)) (u v : α) (huv : u ≠ v)
    (hf : IsFaceOf (↑facets : Set (Finset α)) {u, v}) (P : MvPolynomial α R) :
    srPairDetector R facets u v huv hf (Ideal.Quotient.mk (stanleyReisnerIdeal R facets) P)
      = MvPolynomial.coeff (Finsupp.single u 1 + Finsupp.single v 1) P := rfl

/-- The pair detector reads the product `x_u x_v` as `1`. -/
theorem srPairDetector_srVertexX_mul (facets : Finset (Finset α)) {u v : α} (huv : u ≠ v)
    (hf : IsFaceOf (↑facets : Set (Finset α)) {u, v}) :
    srPairDetector R facets u v huv hf (srVertexX R facets u * srVertexX R facets v) = 1 := by
  rw [srVertexX, srVertexX, ← map_mul, srPairDetector_mk,
    show (X u * X v : MvPolynomial α R) = monomial (Finsupp.single u 1 + Finsupp.single v 1) 1 by
      rw [MvPolynomial.X, MvPolynomial.X, MvPolynomial.monomial_mul]; simp,
    MvPolynomial.coeff_monomial, if_pos rfl]

/-- **Pair-detector product rule.**  Multiplying by `x_j` and reading the `x_u x_v` coefficient drops
to a degree-one detector: it reads the `x_v` coefficient when `j = u`, the `x_u` coefficient when
`j = v`, and vanishes otherwise.  This links the degree-two detector to the degree-one detectors and
is the mechanism behind the empty-triangle boundary cancellation. -/
theorem srPairDetector_mul_srVertexX (facets : Finset (Finset α)) {u v j : α} (huv : u ≠ v)
    (hf : IsFaceOf (↑facets : Set (Finset α)) {u, v}) (hu : IsFaceOf (↑facets : Set (Finset α)) {u})
    (hv : IsFaceOf (↑facets : Set (Finset α)) {v}) (r : stanleyReisnerRing R facets) :
    srPairDetector R facets u v huv hf (r * srVertexX R facets j)
      = if j = u then srH0Detector R facets v hv r
        else if j = v then srH0Detector R facets u hu r else 0 := by
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective r
  rw [srVertexX, ← map_mul, srPairDetector_mk, srH0Detector_mk, srH0Detector_mk,
    MvPolynomial.coeff_mul_X', support_single_add_single huv]
  by_cases hju : j = u
  · subst hju
    rw [if_pos (Finset.mem_insert_self _ _), add_tsub_cancel_left, if_pos rfl]
  · by_cases hjv : j = v
    · subst hjv
      rw [if_pos (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)),
        add_tsub_cancel_right, if_neg hju, if_pos rfl]
    · rw [if_neg (by simp [hju, hjv]), if_neg hju, if_neg hjv]

/-- The squarefree indicator exponent of a set has that set as support. -/
theorem support_indicatorExponent (J : Finset α) : (indicatorExponent J).support = J := by
  rw [indicatorExponent]; exact GaloisForLFunctions.VeroneseIdeal.support_sum_single J

/-- **General face detector.**  The squarefree `∏_{v∈J} x_v`-coefficient reader descended to the
Stanley–Reisner ring, well-defined for any face `J`.  It subsumes the degree-zero (`J = ∅`),
degree-one (`J = {w}`), and degree-two (`J = {u,v}`) detectors. -/
noncomputable def srFaceDetector (R : Type*) [CommRing R] (facets : Finset (Finset α))
    (J : Finset α) (hJ : IsFaceOf (↑facets : Set (Finset α)) J) :
    stanleyReisnerRing R facets →ₗ[R] R :=
  Submodule.liftQ ((stanleyReisnerIdeal R facets).restrictScalars R)
    (MvPolynomial.lcoeff R (indicatorExponent J))
    (by
      intro P hP
      rw [Submodule.restrictScalars_mem] at hP
      rw [LinearMap.mem_ker, MvPolynomial.lcoeff_apply]
      refine coeff_eq_zero_of_isFace_support facets ?_ hP
      rw [support_indicatorExponent]; exact hJ)

@[simp]
theorem srFaceDetector_mk (facets : Finset (Finset α)) (J : Finset α)
    (hJ : IsFaceOf (↑facets : Set (Finset α)) J) (P : MvPolynomial α R) :
    srFaceDetector R facets J hJ (Ideal.Quotient.mk (stanleyReisnerIdeal R facets) P)
      = MvPolynomial.coeff (indicatorExponent J) P := rfl

/-- The face detector reads its own squarefree monomial `∏_{v∈J} x_v` as `1`. -/
theorem srFaceDetector_prod (facets : Finset (Finset α)) (J : Finset α)
    (hJ : IsFaceOf (↑facets : Set (Finset α)) J) :
    srFaceDetector R facets J hJ (∏ v ∈ J, srVertexX R facets v) = 1 := by
  rw [show (∏ v ∈ J, srVertexX R facets v)
        = Ideal.Quotient.mk (stanleyReisnerIdeal R facets) (∏ v ∈ J, X v) by rw [map_prod]; rfl,
    srFaceDetector_mk, GaloisForLFunctions.VeroneseIdeal.prod_X_eq_monomial]
  simp [indicatorExponent, MvPolynomial.coeff_monomial]

/-- Splitting off a member vertex from a squarefree indicator exponent. -/
theorem indicatorExponent_erase {J : Finset α} {j : α} (hj : j ∈ J) :
    indicatorExponent J = Finsupp.single j 1 + indicatorExponent (J.erase j) := by
  rw [indicatorExponent, indicatorExponent, ← Finset.add_sum_erase J _ hj]

/-- **General face-detector product rule.**  Multiplying by `x_j` and reading the `∏_{v∈J} x_v`
coefficient drops to the deleted-vertex face detector when `j ∈ J`, and vanishes otherwise. -/
theorem srFaceDetector_mul_srVertexX (facets : Finset (Finset α)) {J : Finset α} {j : α}
    (hJ : IsFaceOf (↑facets : Set (Finset α)) J) (r : stanleyReisnerRing R facets) :
    srFaceDetector R facets J hJ (r * srVertexX R facets j)
      = if j ∈ J then
          srFaceDetector R facets (J.erase j) (isFaceOf_mono (Finset.erase_subset j J) hJ) r
        else 0 := by
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective r
  rw [srVertexX, ← map_mul, srFaceDetector_mk, MvPolynomial.coeff_mul_X',
    support_indicatorExponent]
  by_cases hj : j ∈ J
  · rw [if_pos hj, if_pos hj, srFaceDetector_mk, indicatorExponent_erase hj,
      add_tsub_cancel_left]
  · rw [if_neg hj, if_neg hj]

variable [Fintype α]

/-- The first Koszul relation of the vertex coordinate family of a Stanley–Reisner ring: the syzygy
value `∑ v aᵥ xᵥ` of a coefficient family `a`. -/
def srKoszulRelation (facets : Finset (Finset α)) (a : α → stanleyReisnerRing R facets) :
    stanleyReisnerRing R facets :=
  ∑ v, a v * srVertexX R facets v

/-- The base-to-component disconnect cycle joining a base vertex `v₀` to a vertex `w`: the vertex
coordinate `x_w` at position `v₀`, zero elsewhere. -/
def srDisconnectCycle (R : Type*) [CommRing R] (facets : Finset (Finset α)) (v₀ w : α) :
    α → stanleyReisnerRing R facets :=
  fun v => if v = v₀ then srVertexX R facets w else 0

/-- **General base-to-component Koszul cycle.**  Whenever `{v₀, w}` is a nonface — in particular
whenever `v₀` and `w` lie in different connected components of the complex's 1-skeleton — the
base-to-`w` disconnect cycle is a first Koszul cycle of the Stanley–Reisner ring.  This is the
uniform form of the concrete disconnect-cycle laws (`isolatedKoszulRelation_disconnectCycle`,
`singleEdgeKoszulRelation_disconnectCycle`) for arbitrary finite complexes. -/
theorem srKoszulRelation_disconnectCycle (facets : Finset (Finset α)) {v₀ w : α}
    (hwv : w ≠ v₀) (hnf : ¬ IsFaceOf (↑facets : Set (Finset α)) {w, v₀}) :
    srKoszulRelation facets (srDisconnectCycle R facets v₀ w) = 0 := by
  classical
  rw [srKoszulRelation, Finset.sum_eq_single v₀]
  · simp only [srDisconnectCycle, if_pos]
    exact srVertexX_mul_eq_zero_of_not_isFace facets hwv hnf
  · intro v _ hv
    simp only [srDisconnectCycle, if_neg hv, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **Empty-triangle syzygy is a first Koszul cycle (degree ≥ 1 / `|σ| = 3`).**  When `{a,b,c}` is a
nonface (in particular the "empty triangle": three mutual edges but no filling 2-face), the syzygy
`xᵦxᵧ · eₐ` at multidegree `{a,b,c}` is a first Koszul cycle, because `xᵦxᵧxₐ = 0` by the general
nonface relation.  Modulo boundaries this carries the Hochster contribution
`Tor_{1,{a,b,c}} = H̃¹(Δ_{{a,b,c}})` — the first place reduced `H̃¹` (a genuine higher strand) appears. -/
theorem srKoszulRelation_emptyTriangleSyzygy (facets : Finset (Finset α)) {a b c : α}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hnf : ¬ IsFaceOf (↑facets : Set (Finset α)) {a, b, c}) :
    srKoszulRelation facets
      (fun v => if v = a then srVertexX R facets b * srVertexX R facets c else 0) = 0 := by
  classical
  rw [srKoszulRelation, Finset.sum_eq_single a]
  · rw [if_pos rfl,
      show srVertexX R facets b * srVertexX R facets c * srVertexX R facets a
          = ∏ v ∈ ({a, b, c} : Finset α), srVertexX R facets v by
        rw [Finset.prod_insert (by simp [hab, hac]), Finset.prod_insert (by simp [hbc]),
          Finset.prod_singleton]; ring]
    exact srProd_eq_zero_of_not_isFace facets hnf
  · intro v _ hv; rw [if_neg hv, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Hollow-tetrahedron syzygy is a first Koszul cycle (`|σ| = 4` / `H̃²`).**  When `{a,b,c,d}` is a
nonface (the hollow tetrahedron `∂Δ³`: every proper face present, no filling `3`-face), the syzygy
`xᵦxᵧx_d · eₐ` at multidegree `{a,b,c,d}` is a first Koszul cycle, since `xᵦxᵧx_d xₐ = 0` by the
general nonface relation.  Modulo boundaries it carries `Tor_{1,{a,b,c,d}} = H̃²(Δ_{{a,b,c,d}})` — the
first place reduced `H̃²` (a genuine second reduced cohomology) appears, still inside `Tor₁`. -/
theorem srKoszulRelation_hollowTetrahedronSyzygy (facets : Finset (Finset α)) {a b c d : α}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hnf : ¬ IsFaceOf (↑facets : Set (Finset α)) {a, b, c, d}) :
    srKoszulRelation facets
        (fun v => if v = a then
          srVertexX R facets b * srVertexX R facets c * srVertexX R facets d else 0) = 0 := by
  classical
  rw [srKoszulRelation, Finset.sum_eq_single a]
  · rw [if_pos rfl,
      show srVertexX R facets b * srVertexX R facets c * srVertexX R facets d * srVertexX R facets a
          = ∏ v ∈ ({a, b, c, d} : Finset α), srVertexX R facets v by
        rw [Finset.prod_insert (by simp [hab, hac, had]), Finset.prod_insert (by simp [hbc, hbd]),
          Finset.prod_insert (by simp [hcd]), Finset.prod_singleton]; ring]
    exact srProd_eq_zero_of_not_isFace facets hnf
  · intro v _ hv; rw [if_neg hv, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Hollow-simplex syzygy is a first Koszul cycle (all dimensions).**  For any nonface `σ` and a
vertex `a ∈ σ`, the syzygy `(∏_{w∈σ∖a} x_w) · eₐ` at multidegree `σ` is a first Koszul cycle, since
`(∏_{w∈σ∖a} x_w) xₐ = ∏_{w∈σ} x_w = 0` by the general nonface relation.  When `σ` is a minimal
nonface (the hollow simplex `∂Δ^{|σ|−1}`) it carries `Tor_{1,σ} = H̃^{|σ|−2}(Δ_σ)`, so this single
theorem realizes the whole reduced-cohomology tower `H̃⁰, H̃¹, H̃², …` as first Koszul cycles.
Subsumes the triangle (`|σ|=3`) and tetrahedron (`|σ|=4`) syzygies. -/
theorem srKoszulRelation_hollowSimplexSyzygy (facets : Finset (Finset α)) {σ : Finset α} {a : α}
    (ha : a ∈ σ) (hnf : ¬ IsFaceOf (↑facets : Set (Finset α)) σ) :
    srKoszulRelation facets
        (fun v => if v = a then ∏ w ∈ σ.erase a, srVertexX R facets w else 0) = 0 := by
  classical
  rw [srKoszulRelation, Finset.sum_eq_single a]
  · rw [if_pos rfl, mul_comm, Finset.mul_prod_erase σ (fun w => srVertexX R facets w) ha]
    exact srProd_eq_zero_of_not_isFace facets hnf
  · intro v _ hv; rw [if_neg hv, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The first Koszul boundary submodule (trivial syzygies), order-free via the antisymmetrization of
an arbitrary coefficient field `c`. -/
def srKoszulBoundary (facets : Finset (Finset α))
    (c : α → α → stanleyReisnerRing R facets) (i : α) : stanleyReisnerRing R facets :=
  ∑ j, (c i j - c j i) * srVertexX R facets j

/-- **General face-detector of a boundary.**  The `J`-face detector of a Koszul boundary at position
`i` is the sum, over `j ∈ J`, of the deleted-vertex face detectors of the antisymmetric coefficient
`c i j − c j i`. -/
theorem srFaceDetector_srKoszulBoundary (facets : Finset (Finset α)) {J : Finset α}
    (hJ : IsFaceOf (↑facets : Set (Finset α)) J)
    (c : α → α → stanleyReisnerRing R facets) (i : α) :
    srFaceDetector R facets J hJ (srKoszulBoundary facets c i)
      = ∑ j ∈ J, srFaceDetector R facets (J.erase j)
          (isFaceOf_mono (Finset.erase_subset j J) hJ) (c i j - c j i) := by
  rw [srKoszulBoundary, map_sum,
    Finset.sum_congr rfl (fun j _ => srFaceDetector_mul_srVertexX facets hJ (c i j - c j i)),
    Finset.sum_ite_mem, Finset.univ_inter]

/-- **Detector of a boundary.**  The `w`-detector of the boundary at position `i` collapses to the
constant term of the single antisymmetric coefficient `c i w − c w i`, because the product-detector
rule kills every term except `j = w`. -/
theorem srH0Detector_srKoszulBoundary (facets : Finset (Finset α))
    (hE : IsFaceOf (↑facets : Set (Finset α)) ∅)
    (c : α → α → stanleyReisnerRing R facets) {w i : α}
    (hw : IsFaceOf (↑facets : Set (Finset α)) {w}) :
    srH0Detector R facets w hw (srKoszulBoundary facets c i)
      = srConstTerm R facets hE (c i w - c w i) := by
  rw [srKoszulBoundary, map_sum,
    Finset.sum_congr rfl (fun j _ => srH0Detector_mul_srVertexX facets hE hw (c i j - c j i)),
    Finset.sum_ite_eq]
  simp

omit [DecidableEq α] in
/-- **Boundaries are cycles (`d₁ ∘ d₂ = 0`).**  Every first Koszul boundary is a first Koszul
cycle: the antisymmetric coefficients pair against the symmetric products `xⱼ xᵢ` and cancel.  This
makes the first Koszul homology `cycles / boundaries` well-defined, so "independent modulo
boundaries" is a statement about a genuine subquotient. -/
theorem srKoszulRelation_srKoszulBoundary (facets : Finset (Finset α))
    (c : α → α → stanleyReisnerRing R facets) :
    srKoszulRelation facets (srKoszulBoundary facets c) = 0 := by
  have key : (∑ i, ∑ j, c j i * srVertexX R facets j * srVertexX R facets i)
      = ∑ i, ∑ j, c i j * srVertexX R facets j * srVertexX R facets i := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [srKoszulRelation]
  have expand : ∀ i, srKoszulBoundary facets c i * srVertexX R facets i
      = ∑ j, (c i j * srVertexX R facets j * srVertexX R facets i
              - c j i * srVertexX R facets j * srVertexX R facets i) := by
    intro i
    rw [srKoszulBoundary, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [expand, Finset.sum_sub_distrib]
  rw [key, sub_self]

omit [Fintype α] in
@[simp]
theorem srDisconnectCycle_apply_self (facets : Finset (Finset α)) (v₀ w : α) :
    srDisconnectCycle R facets v₀ w v₀ = srVertexX R facets w := by
  simp [srDisconnectCycle]

omit [Fintype α] in
theorem srDisconnectCycle_apply_of_ne (facets : Finset (Finset α)) (v₀ w : α) {i : α}
    (hi : i ≠ v₀) : srDisconnectCycle R facets v₀ w i = 0 := by
  simp [srDisconnectCycle, hi]

/-- **General degree-0 Hochster independence.**  For a complex with all vertices present and a base
vertex `v₀`, the base-to-component disconnect cycles are linearly independent modulo first Koszul
boundaries: any linear combination that is a boundary has all non-base coefficients zero.  Thus the
first Koszul quotient carries the full reduced-`H̃⁰` rank (`components − 1`), uniformly over all
finite complexes.  The proof applies the symmetric detector `Φ_w(a) = D_w(a v₀) + D_{v₀}(a w)`, which
reads off each coefficient (Kronecker duality) yet annihilates every boundary. -/
theorem srDisconnectCycle_independent_mod_koszulBoundary (facets : Finset (Finset α))
    (hE : IsFaceOf (↑facets : Set (Finset α)) ∅)
    (hverts : ∀ v : α, IsFaceOf (↑facets : Set (Finset α)) {v})
    (v₀ : α) (a : α → R) (c : α → α → stanleyReisnerRing R facets)
    (h : (∑ w, a w • srDisconnectCycle R facets v₀ w) = srKoszulBoundary facets c) :
    ∀ w, w ≠ v₀ → a w = 0 := by
  intro w hw
  have hwf := hverts w
  have hv0f := hverts v₀
  have hA : srH0Detector R facets w hwf
      ((∑ w', a w' • srDisconnectCycle R facets v₀ w') v₀) = a w := by
    rw [Finset.sum_apply, map_sum, Finset.sum_eq_single w]
    · simp
    · intro w' _ hne
      simp [srH0Detector_srVertexX, Ne.symm hne]
    · intro hc; exact absurd (Finset.mem_univ _) hc
  have hB : srH0Detector R facets v₀ hv0f
      ((∑ w', a w' • srDisconnectCycle R facets v₀ w') w) = 0 := by
    rw [Finset.sum_apply]
    simp [srDisconnectCycle_apply_of_ne facets v₀ _ hw]
  have hR : srH0Detector R facets w hwf (srKoszulBoundary facets c v₀)
      + srH0Detector R facets v₀ hv0f (srKoszulBoundary facets c w) = 0 := by
    rw [srH0Detector_srKoszulBoundary facets hE, srH0Detector_srKoszulBoundary facets hE,
      ← map_add, show (c v₀ w - c w v₀) + (c w v₀ - c v₀ w) = 0 by ring, map_zero]
  calc a w = a w + 0 := (add_zero _).symm
    _ = srH0Detector R facets w hwf (srKoszulBoundary facets c v₀)
        + srH0Detector R facets v₀ hv0f (srKoszulBoundary facets c w) := by
          rw [← hA, ← hB, congrFun h v₀, congrFun h w]
    _ = 0 := hR

/-- **Nonzero first-Koszul-homology class (Hochster `Tor₁` at a two-element support).**  For a
complex with every vertex present and a non-base vertex `w`, the base-to-`w` disconnect cycle is not
a first Koszul boundary.  When `{v₀, w}` is additionally a nonface it is a genuine first Koszul
cycle, hence a nonzero class of `Tor₁` at multidegree `{v₀, w}` — the Hochster contribution
`H̃⁰(Δ_{{v₀,w}})` of the induced two-vertex subcomplex (which is `1`-dimensional exactly for a
nonedge).  This is the lowest strand `i = 1, |σ| = 2` of Hochster's formula, not the whole-complex
reduced `H̃⁰`. -/
theorem srDisconnectCycle_not_koszulBoundary [Nontrivial R] (facets : Finset (Finset α))
    (hE : IsFaceOf (↑facets : Set (Finset α)) ∅)
    (hverts : ∀ v : α, IsFaceOf (↑facets : Set (Finset α)) {v})
    {v₀ w : α} (hw : w ≠ v₀) :
    ¬ ∃ c : α → α → stanleyReisnerRing R facets,
      srKoszulBoundary facets c = srDisconnectCycle R facets v₀ w := by
  rintro ⟨c, hc⟩
  have hcoef := srDisconnectCycle_independent_mod_koszulBoundary facets hE hverts v₀
    (fun u => if u = w then (1 : R) else 0) c (by
      rw [Finset.sum_eq_single w]
      · simpa using hc.symm
      · intro u _ hu; simp only [if_neg hu, zero_smul]
      · intro hcontra; exact absurd (Finset.mem_univ _) hcontra) w hw
  simp at hcoef

/-- **Pair-detector of a boundary.**  The `x_u x_v`-detector of the Koszul boundary at position `i`
collapses (via the product rule) to a sum of two degree-one detectors of the antisymmetric
coefficients. -/
theorem srPairDetector_srKoszulBoundary (facets : Finset (Finset α)) {u v : α} (huv : u ≠ v)
    (hf : IsFaceOf (↑facets : Set (Finset α)) {u, v}) (hu : IsFaceOf (↑facets : Set (Finset α)) {u})
    (hv : IsFaceOf (↑facets : Set (Finset α)) {v})
    (c : α → α → stanleyReisnerRing R facets) (i : α) :
    srPairDetector R facets u v huv hf (srKoszulBoundary facets c i)
      = srH0Detector R facets v hv (c i u - c u i)
        + srH0Detector R facets u hu (c i v - c v i) := by
  rw [srKoszulBoundary, map_sum]
  have step : ∀ j, srPairDetector R facets u v huv hf ((c i j - c j i) * srVertexX R facets j)
      = (if j = u then srH0Detector R facets v hv (c i j - c j i) else 0)
        + (if j = v then srH0Detector R facets u hu (c i j - c j i) else 0) := by
    intro j
    rw [srPairDetector_mul_srVertexX facets huv hf hu hv]
    by_cases hju : j = u <;> by_cases hjv : j = v <;> simp_all
  rw [Finset.sum_congr rfl (fun j _ => step j), Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq', if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _)]

/-- **First nonzero reduced-`H̃¹` Hochster class.**  On an empty triangle `{a,b,c}` — all three edges
present, no filling 2-face — the syzygy `xᵦxᵧ · eₐ` is not a first Koszul boundary, so it is a nonzero
class of `Tor₁` at multidegree `{a,b,c}`, i.e. of `H̃¹(Δ_{{a,b,c}})`.  The cyclic degree-two detector
`Φ(s) = D_{bc}(sₐ) + D_{ac}(s_b) + D_{ab}(s_c)` evaluates to `1` on the syzygy but to `0` on every
boundary — its degree-one detector terms cancel in antisymmetric pairs. -/
theorem srEmptyTriangleSyzygy_not_koszulBoundary [Nontrivial R] (facets : Finset (Finset α))
    {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hfab : IsFaceOf (↑facets : Set (Finset α)) {a, b})
    (hfbc : IsFaceOf (↑facets : Set (Finset α)) {b, c})
    (hfac : IsFaceOf (↑facets : Set (Finset α)) {a, c})
    (ha : IsFaceOf (↑facets : Set (Finset α)) {a}) (hb : IsFaceOf (↑facets : Set (Finset α)) {b})
    (hc : IsFaceOf (↑facets : Set (Finset α)) {c}) :
    ¬ ∃ cc : α → α → stanleyReisnerRing R facets,
      srKoszulBoundary facets cc
        = (fun v => if v = a then srVertexX R facets b * srVertexX R facets c else 0) := by
  rintro ⟨cc, hcc⟩
  have hbdry : srPairDetector R facets b c hbc hfbc (srKoszulBoundary facets cc a)
      + (srPairDetector R facets a c hac hfac (srKoszulBoundary facets cc b)
         + srPairDetector R facets a b hab hfab (srKoszulBoundary facets cc c)) = 0 := by
    rw [srPairDetector_srKoszulBoundary facets hbc hfbc hb hc,
      srPairDetector_srKoszulBoundary facets hac hfac ha hc,
      srPairDetector_srKoszulBoundary facets hab hfab ha hb]
    have ec : srH0Detector R facets c hc (cc a b - cc b a)
        + srH0Detector R facets c hc (cc b a - cc a b) = 0 := by
      rw [← map_add, show cc a b - cc b a + (cc b a - cc a b) = 0 by abel, map_zero]
    have eb : srH0Detector R facets b hb (cc a c - cc c a)
        + srH0Detector R facets b hb (cc c a - cc a c) = 0 := by
      rw [← map_add, show cc a c - cc c a + (cc c a - cc a c) = 0 by abel, map_zero]
    have ea : srH0Detector R facets a ha (cc b c - cc c b)
        + srH0Detector R facets a ha (cc c b - cc b c) = 0 := by
      rw [← map_add, show cc b c - cc c b + (cc c b - cc b c) = 0 by abel, map_zero]
    linear_combination ec + eb + ea
  rw [hcc] at hbdry
  simp [Ne.symm hab, Ne.symm hac, srPairDetector_srVertexX_mul facets hbc hfbc] at hbdry

omit [Fintype α] in
/-- An antisymmetric function summed over the "ordered distinct pairs from `σ`" vanishes, by the
`(i,j) ↦ (j,i)` involution. -/
theorem antisym_sigma_sum_zero {M : Type*} [AddCommGroup M] (σ : Finset α) (f : α → α → M)
    (hanti : ∀ i j, f i j + f j i = 0) :
    ∑ p ∈ σ.sigma (fun i => σ.erase i), f p.1 p.2 = 0 := by
  apply Finset.sum_involution (fun p _ => (⟨p.2, p.1⟩ : Σ _ : α, α))
  · intro p _; exact hanti p.1 p.2
  · intro p hp _ hcon
    rw [Finset.mem_sigma] at hp
    exact (Finset.ne_of_mem_erase hp.2) (congrArg Sigma.fst hcon)
  · intro p hp
    rw [Finset.mem_sigma] at hp
    exact Finset.mem_sigma.mpr ⟨Finset.mem_of_mem_erase hp.2,
      Finset.mem_erase.mpr ⟨Ne.symm (Finset.ne_of_mem_erase hp.2), hp.1⟩⟩
  · intro p _; rfl

/-- **Uniform hollow-simplex non-boundary (every reduced-cohomology dimension).**  When every
codimension-one face `σ ∖ i` of a nonface `σ` is a face (`σ` a minimal nonface = hollow simplex
`∂Δ^{|σ|−1}`) and `a ∈ σ`, the syzygy `(∏_{w∈σ∖a} x_w)·eₐ` is not a first Koszul boundary — a nonzero
class of `Tor_{1,σ} = H̃^{|σ|−2}(Δ_σ)`.  The alternating(all-plus) detector
`Φ_σ(s) = ∑_{i∈σ} srFaceDetector(σ∖i)(sᵢ)` is `1` on the syzygy and `0` on every boundary (its
double sum over ordered pairs cancels by the `(i,j)↔(j,i)` involution, unconditionally).  This single
theorem yields the whole tower `H̃⁰, H̃¹, H̃², …` of nonzero Hochster `Tor₁` classes. -/
theorem srHollowSimplexSyzygy_not_koszulBoundary [Nontrivial R] (facets : Finset (Finset α))
    {σ : Finset α} {a : α} (ha : a ∈ σ)
    (hface : ∀ i ∈ σ, IsFaceOf (↑facets : Set (Finset α)) (σ.erase i)) :
    ¬ ∃ cc : α → α → stanleyReisnerRing R facets,
      srKoszulBoundary facets cc
        = (fun v => if v = a then ∏ w ∈ σ.erase a, srVertexX R facets w else 0) := by
  classical
  rintro ⟨cc, hcc⟩
  -- guarded pair coefficient for the double sum
  set f : α → α → R := fun i j =>
    if h : IsFaceOf (↑facets : Set (Finset α)) ((σ.erase i).erase j) then
      srFaceDetector R facets ((σ.erase i).erase j) h (cc i j - cc j i) else 0 with hf
  have f_anti : ∀ i j, f i j + f j i = 0 := by
    intro i j
    simp only [hf]
    rw [show (σ.erase j).erase i = (σ.erase i).erase j from Finset.erase_right_comm]
    by_cases hfc : IsFaceOf (↑facets : Set (Finset α)) ((σ.erase i).erase j)
    · rw [dif_pos hfc, dif_pos hfc, ← map_add]
      rw [show (cc i j - cc j i) + (cc j i - cc i j) = 0 by abel, map_zero]
    · rw [dif_neg hfc, dif_neg hfc, add_zero]
  -- Φ_σ(boundary) = 0
  have hbdry : (∑ i ∈ σ, if h : IsFaceOf (↑facets : Set (Finset α)) (σ.erase i) then
        srFaceDetector R facets (σ.erase i) h (srKoszulBoundary facets cc i) else 0) = 0 := by
    rw [Finset.sum_congr rfl (fun i hi => ?_), Finset.sum_sigma']
    · exact antisym_sigma_sum_zero σ f f_anti
    · rw [dif_pos (hface i hi), srFaceDetector_srKoszulBoundary facets (hface i hi) cc i]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      simp only [hf]
      rw [dif_pos (isFaceOf_mono (Finset.erase_subset j (σ.erase i)) (hface i hi))]
  -- Φ_σ(syzygy) = 1
  have hsyz : (∑ i ∈ σ, if h : IsFaceOf (↑facets : Set (Finset α)) (σ.erase i) then
        srFaceDetector R facets (σ.erase i) h
          ((fun v => if v = a then ∏ w ∈ σ.erase a, srVertexX R facets w else 0) i) else 0) = 1 := by
    rw [Finset.sum_eq_single a]
    · rw [dif_pos (hface a ha)]
      simp only []
      exact srFaceDetector_prod facets (σ.erase a) (hface a ha)
    · intro i _ hia
      by_cases hfi : IsFaceOf (↑facets : Set (Finset α)) (σ.erase i)
      · rw [dif_pos hfi]; simp only [if_neg hia]; exact map_zero _
      · rw [dif_neg hfi]
    · intro h; exact absurd ha h
  rw [hcc] at hbdry
  exact one_ne_zero (hbdry.symm.trans hsyz).symm

/-- **Hollow simplex carries a nonzero first Koszul homology class (every dimension).**  The general
capstone of the `Tor₁` layer: for a minimal nonface `σ` (hollow simplex `∂Δ^{|σ|−1}`, every proper
face present) and `a ∈ σ`, the syzygy `(∏_{w∈σ∖a} x_w)·eₐ` is a first Koszul cycle that is not a first
Koszul boundary — a nonzero class in the first Koszul homology `Tor₁` at multidegree `σ`, i.e. in
`H̃^{|σ|−2}(Δ_σ)`.  Ranging over `|σ| = n+2` this realizes every reduced cohomology `H̃ⁿ` as a nonzero
Hochster `Tor₁` class; it subsumes the empty-triangle (`H̃¹`) statement. -/
theorem srHollowSimplex_firstKoszulHomology_nonzero [Nontrivial R] (facets : Finset (Finset α))
    {σ : Finset α} {a : α} (ha : a ∈ σ)
    (hnf : ¬ IsFaceOf (↑facets : Set (Finset α)) σ)
    (hface : ∀ i ∈ σ, IsFaceOf (↑facets : Set (Finset α)) (σ.erase i)) :
    srKoszulRelation facets
        (fun v => if v = a then ∏ w ∈ σ.erase a, srVertexX R facets w else 0) = 0
      ∧ ¬ ∃ cc : α → α → stanleyReisnerRing R facets,
        srKoszulBoundary facets cc
          = (fun v => if v = a then ∏ w ∈ σ.erase a, srVertexX R facets w else 0) :=
  ⟨srKoszulRelation_hollowSimplexSyzygy facets ha hnf,
    srHollowSimplexSyzygy_not_koszulBoundary facets ha hface⟩

/-- **Empty triangle carries a nonzero first Koszul homology class.**  Packaging the degree-1 result:
on an empty triangle `{a,b,c}` (three edges, no filling 2-face, all vertices present), the syzygy
`xᵦxᵧ · eₐ` is a first Koszul cycle that is not a first Koszul boundary.  It therefore represents a
nonzero class in the first Koszul homology `Tor₁` at multidegree `{a,b,c}`, i.e. in
`H̃¹(Δ_{{a,b,c}})` — the reduced first cohomology of the induced triangle hole. -/
theorem srEmptyTriangle_firstKoszulHomology_nonzero [Nontrivial R] (facets : Finset (Finset α))
    {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hfab : IsFaceOf (↑facets : Set (Finset α)) {a, b})
    (hfbc : IsFaceOf (↑facets : Set (Finset α)) {b, c})
    (hfac : IsFaceOf (↑facets : Set (Finset α)) {a, c})
    (ha : IsFaceOf (↑facets : Set (Finset α)) {a}) (hb : IsFaceOf (↑facets : Set (Finset α)) {b})
    (hc : IsFaceOf (↑facets : Set (Finset α)) {c})
    (hnf : ¬ IsFaceOf (↑facets : Set (Finset α)) {a, b, c}) :
    srKoszulRelation facets
        (fun v => if v = a then srVertexX R facets b * srVertexX R facets c else 0) = 0
      ∧ ¬ ∃ cc : α → α → stanleyReisnerRing R facets,
        srKoszulBoundary facets cc
          = (fun v => if v = a then srVertexX R facets b * srVertexX R facets c else 0) :=
  ⟨srKoszulRelation_emptyTriangleSyzygy facets hab hac hbc hnf,
    srEmptyTriangleSyzygy_not_koszulBoundary facets hab hac hbc hfab hfbc hfac ha hb hc⟩

/-- **The empty-triangle class is cyclically symmetric.**  The two cyclic syzygies `xᵦxᵧ · eₐ` and
`xₐxᵧ · e_b` differ by an explicit first Koszul boundary, hence represent the *same* class in the
first Koszul homology — the `1`-dimensional `H̃¹` of the triangle hole is generated by any of its
three cyclic representatives. -/
theorem srEmptyTriangle_cyclic_syzygy_homologous (facets : Finset (Finset α)) (a b c : α)
    (hab : a ≠ b) :
    srKoszulBoundary facets (fun i j => if i = a ∧ j = b then srVertexX R facets c else 0)
      = (fun v => if v = a then srVertexX R facets b * srVertexX R facets c else 0)
        - (fun v => if v = b then srVertexX R facets a * srVertexX R facets c else 0) := by
  classical
  funext v
  rw [srKoszulBoundary, Pi.sub_apply]
  by_cases hva : v = a
  · subst hva
    rw [Finset.sum_eq_single b (fun j _ hjb => by simp [hab, hjb])
      (fun h => absurd (Finset.mem_univ _) h)]
    simp [hab, mul_comm]
  · by_cases hvb : v = b
    · subst hvb
      rw [Finset.sum_eq_single a (fun j _ hja => by simp [hja, Ne.symm hab])
        (fun h => absurd (Finset.mem_univ _) h)]
      simp [hab, Ne.symm hab]
      ring
    · rw [Finset.sum_eq_zero (fun j _ => by simp [hva, hvb])]
      simp [hva, hvb]

omit [DecidableEq α] in
/-- An antisymmetric function with zero diagonal, summed over `σ × σ`, vanishes by the `Prod.swap`
involution. -/
theorem antisym_prod_sum_zero {M : Type*} [AddCommGroup M] (g : α → α → M)
    (hanti : ∀ i j, g i j + g j i = 0) (hdiag : ∀ i, g i i = 0) :
    ∑ p ∈ (Finset.univ ×ˢ Finset.univ : Finset (α × α)), g p.1 p.2 = 0 := by
  apply Finset.sum_involution (fun p _ => Prod.swap p)
  · intro p _; exact hanti p.1 p.2
  · intro p _ hne hcon
    apply hne
    have hp : p.2 = p.1 := congrArg Prod.fst hcon
    rw [hp]; exact hdiag p.1
  · intro p _; simp
  · intro p _; simp

/-- An alternating 3-tensor: antisymmetric under adjacent transpositions and vanishing whenever two
indices coincide — the coefficient shape of the degree-three Koszul term. -/
structure IsAlternating3 {M : Type*} [AddCommGroup M] (b : α → α → α → M) : Prop where
  antisym12 : ∀ i j k, b i j k = - b j i k
  antisym23 : ∀ i j k, b i j k = - b i k j
  alt : ∀ i j k, i = j ∨ j = k ∨ i = k → b i j k = 0

/-- The third Koszul differential `d₃` (degree 3 → 2): `d₃(b)_{ij} = ∑_k b_{ijk} x_k`. -/
def srKoszulBoundary3 (facets : Finset (Finset α))
    (b : α → α → α → stanleyReisnerRing R facets) (i j : α) : stanleyReisnerRing R facets :=
  ∑ k, b i j k * srVertexX R facets k

omit [DecidableEq α] in
/-- **`d₂ ∘ d₃ = 0`.**  The Koszul complex extends to degree three: applying the second differential to
`d₃` of an alternating 3-tensor gives zero, so the second Koszul homology `Tor₂` is a well-defined
subquotient.  The alternating coefficients pair against the symmetric products `xₖxⱼ` and cancel by
the `(j,k)↔(k,j)` involution, unconditionally (no characteristic hypothesis). -/
theorem srKoszulBoundary_srKoszulBoundary3 (facets : Finset (Finset α))
    {b : α → α → α → stanleyReisnerRing R facets} (hb : IsAlternating3 b) :
    srKoszulBoundary facets (srKoszulBoundary3 facets b) = 0 := by
  have prodsum : ∀ (φ : α → α → stanleyReisnerRing R facets),
      (∀ j k, φ j k * srVertexX R facets k * srVertexX R facets j
        + φ k j * srVertexX R facets j * srVertexX R facets k = 0) →
      (∀ j, φ j j * srVertexX R facets j * srVertexX R facets j = 0) →
      (∑ j, ∑ k, φ j k * srVertexX R facets k * srVertexX R facets j) = 0 := by
    intro φ ha hd
    rw [← Finset.sum_product']
    exact antisym_prod_sum_zero
      (fun j k => φ j k * srVertexX R facets k * srVertexX R facets j) ha hd
  funext i
  simp only [Pi.zero_apply]
  rw [srKoszulBoundary]
  simp only [srKoszulBoundary3, sub_mul, Finset.sum_mul, Finset.sum_sub_distrib]
  rw [prodsum (b i)
      (fun j k => by rw [hb.antisym23 i j k]; ring)
      (fun j => by rw [hb.alt i j j (Or.inr (Or.inl rfl))]; ring),
    prodsum (fun j k => b j i k)
      (fun j k => by
        show b j i k * srVertexX R facets k * srVertexX R facets j
          + b k i j * srVertexX R facets j * srVertexX R facets k = 0
        have hkij : b k i j = - b j i k := by
          rw [hb.antisym12 k i j, hb.antisym23 i k j, hb.antisym12 j i k]
        rw [hkij]; ring)
      (fun j => by
        show b j i j * srVertexX R facets j * srVertexX R facets j = 0
        rw [hb.alt j i j (Or.inr (Or.inr rfl))]; ring),
    sub_zero]

omit [DecidableEq α] in
/-- **Third-differential boundaries are antisymmetric.**  `d₃` of an alternating 3-tensor is an
antisymmetric 2-tensor, so `im d₃` lands in the alternating part `K₂` of the Koszul complex — the
correct home for `Tor₂` representatives. -/
theorem srKoszulBoundary3_antisymm (facets : Finset (Finset α))
    {b : α → α → α → stanleyReisnerRing R facets} (hb : IsAlternating3 b) (i j : α) :
    srKoszulBoundary3 facets b j i = - srKoszulBoundary3 facets b i j := by
  refine eq_neg_of_add_eq_zero_left ?_
  rw [srKoszulBoundary3, srKoszulBoundary3, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero (fun k _ => ?_)
  rw [hb.antisym12 j i k]; ring

/-- An alternating 4-tensor: antisymmetric under adjacent transpositions and vanishing whenever two
indices coincide — the coefficient shape of the degree-four Koszul term. -/
structure IsAlternating4 {M : Type*} [AddCommGroup M] (b : α → α → α → α → M) : Prop where
  antisym12 : ∀ i j k l, b i j k l = - b j i k l
  antisym23 : ∀ i j k l, b i j k l = - b i k j l
  antisym34 : ∀ i j k l, b i j k l = - b i j l k
  alt : ∀ i j k l, i = j ∨ j = k ∨ k = l ∨ i = k ∨ j = l ∨ i = l → b i j k l = 0

/-- The fourth Koszul differential `d₄` (degree 4 → 3): `d₄(b)_{ijk} = ∑_l b_{ijkl} x_l`. -/
def srKoszulBoundary4 (facets : Finset (Finset α))
    (b : α → α → α → α → stanleyReisnerRing R facets) (i j k : α) : stanleyReisnerRing R facets :=
  ∑ l, b i j k l * srVertexX R facets l

omit [DecidableEq α] in
/-- **`d₃ ∘ d₄ = 0`.**  The Koszul complex extends to degree four: applying the third differential to
`d₄` of an alternating 4-tensor gives zero, so the third Koszul homology `Tor₃` is a well-defined
subquotient.  The composite is `∑_{k,l} b_{ijkl} xₗxₖ`, which cancels by the `(k,l)↔(l,k)` involution
against the symmetric products, unconditionally. -/
theorem srKoszulBoundary3_srKoszulBoundary4 (facets : Finset (Finset α))
    {b : α → α → α → α → stanleyReisnerRing R facets} (hb : IsAlternating4 b) :
    srKoszulBoundary3 facets (srKoszulBoundary4 facets b) = 0 := by
  funext i j
  simp only [Pi.zero_apply, srKoszulBoundary3, srKoszulBoundary4, Finset.sum_mul]
  rw [← Finset.sum_product']
  exact antisym_prod_sum_zero
    (fun k l => b i j k l * srVertexX R facets l * srVertexX R facets k)
    (fun k l => by
      show b i j k l * srVertexX R facets l * srVertexX R facets k
        + b i j l k * srVertexX R facets k * srVertexX R facets l = 0
      rw [hb.antisym34 i j l k]; ring)
    (fun k => by
      show b i j k k * srVertexX R facets k * srVertexX R facets k = 0
      rw [hb.alt i j k k (Or.inr (Or.inr (Or.inl rfl)))]; ring)

omit [DecidableEq α] in
/-- **Fourth-differential boundaries are alternating 3-tensors.**  `d₄` of an alternating 4-tensor is
an alternating 3-tensor, so `im d₄` lands in the alternating part `K₃` of the Koszul complex — the
correct home for `Tor₃` representatives.  This completes the `Tor₃` foundation alongside `d₃∘d₄=0`. -/
theorem srKoszulBoundary4_alternating (facets : Finset (Finset α))
    {b : α → α → α → α → stanleyReisnerRing R facets} (hb : IsAlternating4 b) :
    IsAlternating3 (srKoszulBoundary4 facets b) := by
  refine ⟨fun i j k => ?_, fun i j k => ?_, fun i j k h => ?_⟩
  · refine eq_neg_of_add_eq_zero_left ?_
    rw [srKoszulBoundary4, srKoszulBoundary4, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun l _ => by rw [hb.antisym12 i j k l]; ring
  · refine eq_neg_of_add_eq_zero_left ?_
    rw [srKoszulBoundary4, srKoszulBoundary4, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun l _ => by rw [hb.antisym23 i j k l]; ring
  · rw [srKoszulBoundary4]
    refine Finset.sum_eq_zero fun l _ => ?_
    have hz : b i j k l = 0 := by
      rcases h with h | h | h
      · exact hb.alt i j k l (Or.inl h)
      · exact hb.alt i j k l (Or.inr (Or.inl h))
      · exact hb.alt i j k l (Or.inr (Or.inr (Or.inr (Or.inl h))))
    rw [hz, zero_mul]

/-- An alternating 5-tensor: antisymmetric under adjacent transpositions and vanishing whenever two
indices coincide — the coefficient shape of the degree-five Koszul term. -/
structure IsAlternating5 {M : Type*} [AddCommGroup M] (b : α → α → α → α → α → M) : Prop where
  antisym12 : ∀ i j k l m, b i j k l m = - b j i k l m
  antisym23 : ∀ i j k l m, b i j k l m = - b i k j l m
  antisym34 : ∀ i j k l m, b i j k l m = - b i j l k m
  antisym45 : ∀ i j k l m, b i j k l m = - b i j k m l
  alt : ∀ i j k l m, i = j ∨ j = k ∨ k = l ∨ l = m ∨ i = k ∨ i = l ∨ i = m ∨ j = l ∨ j = m ∨ k = m →
    b i j k l m = 0

/-- The fifth Koszul differential `d₅` (degree 5 → 4): `d₅(b)_{ijkl} = ∑_m b_{ijklm} x_m`. -/
def srKoszulBoundary5 (facets : Finset (Finset α))
    (b : α → α → α → α → α → stanleyReisnerRing R facets) (i j k l : α) :
    stanleyReisnerRing R facets :=
  ∑ m, b i j k l m * srVertexX R facets m

omit [DecidableEq α] in
/-- **`d₄ ∘ d₅ = 0`.**  The Koszul complex extends to degree five: the fourth differential of `d₅` of
an alternating 5-tensor vanishes, so the fourth Koszul homology `Tor₄` is a well-defined subquotient.
The composite `∑_{l,m} b_{ijklm} xₘxₗ` cancels by the `(l,m)↔(m,l)` involution, unconditionally. -/
theorem srKoszulBoundary4_srKoszulBoundary5 (facets : Finset (Finset α))
    {b : α → α → α → α → α → stanleyReisnerRing R facets} (hb : IsAlternating5 b) :
    srKoszulBoundary4 facets (srKoszulBoundary5 facets b) = 0 := by
  funext i j k
  simp only [Pi.zero_apply, srKoszulBoundary4, srKoszulBoundary5, Finset.sum_mul]
  rw [← Finset.sum_product']
  exact antisym_prod_sum_zero
    (fun l m => b i j k l m * srVertexX R facets m * srVertexX R facets l)
    (fun l m => by
      show b i j k l m * srVertexX R facets m * srVertexX R facets l
        + b i j k m l * srVertexX R facets l * srVertexX R facets m = 0
      rw [hb.antisym45 i j k m l]; ring)
    (fun l => by
      show b i j k l l * srVertexX R facets l * srVertexX R facets l = 0
      rw [hb.alt i j k l l (Or.inr (Or.inr (Or.inr (Or.inl rfl))))]; ring)

omit [DecidableEq α] in
/-- **Fifth-differential boundaries are alternating 4-tensors.**  `d₅` of an alternating 5-tensor is an
alternating 4-tensor, so `im d₅` lands in the alternating part `K₄` — the correct home for `Tor₄`
representatives.  This completes the `Tor₄` foundation alongside `d₄∘d₅=0`. -/
theorem srKoszulBoundary5_alternating (facets : Finset (Finset α))
    {b : α → α → α → α → α → stanleyReisnerRing R facets} (hb : IsAlternating5 b) :
    IsAlternating4 (srKoszulBoundary5 facets b) := by
  refine ⟨fun i j k l => ?_, fun i j k l => ?_, fun i j k l => ?_, fun i j k l h => ?_⟩
  · refine eq_neg_of_add_eq_zero_left ?_
    rw [srKoszulBoundary5, srKoszulBoundary5, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun m _ => by rw [hb.antisym12 i j k l m]; ring
  · refine eq_neg_of_add_eq_zero_left ?_
    rw [srKoszulBoundary5, srKoszulBoundary5, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun m _ => by rw [hb.antisym23 i j k l m]; ring
  · refine eq_neg_of_add_eq_zero_left ?_
    rw [srKoszulBoundary5, srKoszulBoundary5, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun m _ => by rw [hb.antisym34 i j k l m]; ring
  · rw [srKoszulBoundary5]
    refine Finset.sum_eq_zero fun m _ => ?_
    have hz : b i j k l m = 0 := by
      rcases h with h | h | h | h | h | h
      · exact hb.alt i j k l m (Or.inl h)
      · exact hb.alt i j k l m (Or.inr (Or.inl h))
      · exact hb.alt i j k l m (Or.inr (Or.inr (Or.inl h)))
      · exact hb.alt i j k l m (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      · exact hb.alt i j k l m (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))
      · exact hb.alt i j k l m (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
    rw [hz, zero_mul]

end

end GaloisForLFunctions.HTGeometry
