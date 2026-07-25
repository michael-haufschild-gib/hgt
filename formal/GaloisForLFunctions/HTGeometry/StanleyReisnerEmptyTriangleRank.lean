import GaloisForLFunctions.HTGeometry.StanleyReisnerVertexRelation

/-!
# Exact first-Koszul rank at an empty triangle (the degree-1 Hochster equality)

For an empty triangle `{a,b,c}` (three edges, no filling `2`-face) the multidegree-`{a,b,c}` first
Koszul syzygies form the three-parameter family

`w(λₐ,λ_b,λ_c) = λₐ · x_b x_c · eₐ + λ_b · x_a x_c · e_b + λ_c · x_a x_b · e_c`.

Every such `w` is a first Koszul cycle (because `x_a x_b x_c = 0`), and this file proves the exact-rank
statement — the genuine Hochster *equality* rather than mere nonvanishing:

`w(λ) is a first Koszul boundary  ↔  λₐ + λ_b + λ_c = 0`.

So the three-dimensional syzygy space collapses to a **one-dimensional** homology, detected by the
coefficient sum: `Tor_{1,{a,b,c}} ≅ k = H̃¹(∂Δ²)`.  The forward direction is the cyclic degree-two
detector `Φ = D_bc + D_ac + D_ab` (which reads `w` as the sum and kills every boundary); the reverse
direction is an explicit spanning construction realizing every sum-zero combination as a boundary of
two single-entry `2`-chains.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

variable {R α : Type*} [CommRing R] [DecidableEq α] [Fintype α]

/-- The multidegree-`{a,b,c}` first Koszul syzygy with coefficients `λₐ,λ_b,λ_c`. -/
noncomputable def srEmptyTriangleSyzygyVec (R : Type*) [CommRing R]
    (facets : Finset (Finset α)) (a b c : α) (la lb lc : R) :
    α → stanleyReisnerRing R facets :=
  fun v => if v = a then la • (srVertexX R facets b * srVertexX R facets c)
    else if v = b then lb • (srVertexX R facets a * srVertexX R facets c)
    else if v = c then lc • (srVertexX R facets a * srVertexX R facets b) else 0

omit [DecidableEq α] in
/-- The first Koszul boundary is additive in its `2`-chain. -/
theorem srKoszulBoundary_add (facets : Finset (Finset α))
    (c c' : α → α → stanleyReisnerRing R facets) :
    srKoszulBoundary facets (fun i j => c i j + c' i j)
      = fun v => srKoszulBoundary facets c v + srKoszulBoundary facets c' v := by
  funext v
  simp only [srKoszulBoundary]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun j _ => by ring)

omit [DecidableEq α] in
/-- The first Koszul boundary is homogeneous in its `2`-chain. -/
theorem srKoszulBoundary_smul (facets : Finset (Finset α)) (r : R)
    (c : α → α → stanleyReisnerRing R facets) :
    srKoszulBoundary facets (fun i j => r • c i j)
      = fun v => r • srKoszulBoundary facets c v := by
  funext v
  simp only [srKoszulBoundary, Finset.smul_sum]
  exact Finset.sum_congr rfl (fun j _ => by rw [← smul_sub, smul_mul_assoc])

/-- **Spanning direction:** every sum-zero syzygy is a first Koszul boundary — the explicit
`2`-chain `−λ_b·⟨a,b⟩⊗x_c − λ_c·⟨a,c⟩⊗x_b` realizes it. -/
theorem srEmptyTriangleSyzygyVec_boundary_of_sum_zero (facets : Finset (Finset α)) {a b c : α}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) {la lb lc : R} (hsum : la + lb + lc = 0) :
    ∃ cc : α → α → stanleyReisnerRing R facets,
      srKoszulBoundary facets cc = srEmptyTriangleSyzygyVec R facets a b c la lb lc := by
  refine ⟨fun i j => (-lb) • (if i = a ∧ j = b then srVertexX R facets c else 0)
      + (-lc) • (if i = a ∧ j = c then srVertexX R facets b else 0), ?_⟩
  rw [srKoszulBoundary_add, srKoszulBoundary_smul, srKoszulBoundary_smul,
    srEmptyTriangle_cyclic_syzygy_homologous facets a b c hab,
    srEmptyTriangle_cyclic_syzygy_homologous facets a c b hac]
  funext v
  simp only [Pi.sub_apply, srEmptyTriangleSyzygyVec]
  by_cases hva : v = a
  · simp only [if_pos hva, if_neg (ne_of_eq_of_ne hva hab), if_neg (ne_of_eq_of_ne hva hac),
      sub_zero, mul_comm (srVertexX R facets c) (srVertexX R facets b)]
    rw [← add_smul, show la = -lb + -lc from by linear_combination hsum]
  · by_cases hvb : v = b
    · simp only [if_neg (ne_of_eq_of_ne hvb (Ne.symm hab)), if_pos hvb,
        if_neg (ne_of_eq_of_ne hvb hbc), sub_zero, zero_sub, smul_zero, add_zero, smul_neg,
        neg_smul, neg_neg]
    · by_cases hvc : v = c
      · simp only [if_neg (ne_of_eq_of_ne hvc (Ne.symm hac)),
          if_neg (ne_of_eq_of_ne hvc (Ne.symm hbc)), if_pos hvc, sub_zero, zero_sub, smul_zero,
          zero_add, smul_neg, neg_smul, neg_neg]
      · simp only [if_neg hva, if_neg hvb, if_neg hvc, sub_zero, smul_zero, add_zero]

/-- **Detector direction:** a syzygy that is a first Koszul boundary has coefficient sum zero — the
cyclic degree-two detector `Φ = D_bc + D_ac + D_ab` reads it as `λₐ+λ_b+λ_c` and annihilates every
boundary. -/
theorem srEmptyTriangleSyzygyVec_sum_zero_of_boundary (facets : Finset (Finset α)) {a b c : α}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hfab : IsFaceOf (↑facets : Set (Finset α)) {a, b})
    (hfbc : IsFaceOf (↑facets : Set (Finset α)) {b, c})
    (hfac : IsFaceOf (↑facets : Set (Finset α)) {a, c})
    (ha : IsFaceOf (↑facets : Set (Finset α)) {a}) (hb : IsFaceOf (↑facets : Set (Finset α)) {b})
    (hc : IsFaceOf (↑facets : Set (Finset α)) {c}) {la lb lc : R}
    (h : ∃ cc : α → α → stanleyReisnerRing R facets,
      srKoszulBoundary facets cc = srEmptyTriangleSyzygyVec R facets a b c la lb lc) :
    la + lb + lc = 0 := by
  obtain ⟨cc, hcc⟩ := h
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
  rw [show srEmptyTriangleSyzygyVec R facets a b c la lb lc a
        = la • (srVertexX R facets b * srVertexX R facets c) from by
      simp only [srEmptyTriangleSyzygyVec, if_true],
    show srEmptyTriangleSyzygyVec R facets a b c la lb lc b
        = lb • (srVertexX R facets a * srVertexX R facets c) from by
      simp only [srEmptyTriangleSyzygyVec, if_neg hab.symm, if_true],
    show srEmptyTriangleSyzygyVec R facets a b c la lb lc c
        = lc • (srVertexX R facets a * srVertexX R facets b) from by
      simp only [srEmptyTriangleSyzygyVec, if_neg hac.symm, if_neg hbc.symm, if_true],
    map_smul, map_smul, map_smul, srPairDetector_srVertexX_mul facets hbc hfbc,
    srPairDetector_srVertexX_mul facets hac hfac, srPairDetector_srVertexX_mul facets hab hfab] at hbdry
  simp only [smul_eq_mul, mul_one] at hbdry
  linear_combination hbdry

/-- **Exact first-Koszul rank at an empty triangle (degree-1 Hochster equality).**  A multidegree
syzygy `λₐ·x_b x_c·eₐ + λ_b·x_a x_c·e_b + λ_c·x_a x_b·e_c` is a first Koszul boundary **iff** its
coefficient sum vanishes.  Thus the three-parameter syzygy space collapses to the one-dimensional
`Tor_{1,{a,b,c}} ≅ H̃¹(∂Δ²)` detected by the coefficient sum. -/
theorem srEmptyTriangleSyzygyVec_boundary_iff (facets : Finset (Finset α)) {a b c : α}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hfab : IsFaceOf (↑facets : Set (Finset α)) {a, b})
    (hfbc : IsFaceOf (↑facets : Set (Finset α)) {b, c})
    (hfac : IsFaceOf (↑facets : Set (Finset α)) {a, c})
    (ha : IsFaceOf (↑facets : Set (Finset α)) {a}) (hb : IsFaceOf (↑facets : Set (Finset α)) {b})
    (hc : IsFaceOf (↑facets : Set (Finset α)) {c}) (la lb lc : R) :
    (∃ cc : α → α → stanleyReisnerRing R facets,
        srKoszulBoundary facets cc = srEmptyTriangleSyzygyVec R facets a b c la lb lc)
      ↔ la + lb + lc = 0 :=
  ⟨fun h => srEmptyTriangleSyzygyVec_sum_zero_of_boundary facets hab hac hbc hfab hfbc hfac
      ha hb hc h,
    fun h => srEmptyTriangleSyzygyVec_boundary_of_sum_zero facets hab hac hbc h⟩

/-- Every multidegree-`{a,b,c}` syzygy is a first Koszul cycle when `{a,b,c}` is a nonface, since the
Koszul relation collapses to `(λₐ+λ_b+λ_c)·x_a x_b x_c = 0`. -/
theorem srEmptyTriangleSyzygyVec_isCycle (facets : Finset (Finset α)) {a b c : α}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hnf : ¬ IsFaceOf (↑facets : Set (Finset α)) {a, b, c}) (la lb lc : R) :
    srKoszulRelation facets (srEmptyTriangleSyzygyVec R facets a b c la lb lc) = 0 := by
  have hprod : srVertexX R facets a * srVertexX R facets b * srVertexX R facets c = 0 := by
    have h3 := srProd_eq_zero_of_not_isFace (R := R) facets hnf
    rw [Finset.prod_insert (by simp [hab, hac]), Finset.prod_insert (by simp [hbc]),
      Finset.prod_singleton] at h3
    linear_combination h3
  rw [srKoszulRelation]
  apply Finset.sum_eq_zero
  intro v _
  simp only [srEmptyTriangleSyzygyVec]
  by_cases hva : v = a
  · rw [if_pos hva, smul_mul_assoc,
      show srVertexX R facets b * srVertexX R facets c * srVertexX R facets v = 0 from by
        rw [hva]; linear_combination hprod, smul_zero]
  · rw [if_neg hva]
    by_cases hvb : v = b
    · rw [if_pos hvb, smul_mul_assoc,
        show srVertexX R facets a * srVertexX R facets c * srVertexX R facets v = 0 from by
          rw [hvb]; linear_combination hprod, smul_zero]
    · rw [if_neg hvb]
      by_cases hvc : v = c
      · rw [if_pos hvc, smul_mul_assoc,
          show srVertexX R facets a * srVertexX R facets b * srVertexX R facets v = 0 from by
            rw [hvc]; linear_combination hprod, smul_zero]
      · rw [if_neg hvc, zero_mul]

end GaloisForLFunctions.HTGeometry
