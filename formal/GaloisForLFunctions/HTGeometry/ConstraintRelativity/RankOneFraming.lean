import Mathlib

/-!
# Rank-one source-naturality rigidity and the framing law

An algebra law on `ℂ ⊕ L` for a one-dimensional line `L`, natural under every line automorphism,
is forced to be the square-zero (dual-number) law: the scaling automorphisms already kill both the
scalar and the line component of the product of two line elements.  So one unframed anomaly line
canonically generates nothing but the classical dual numbers.

After a frame is chosen, every unital two-dimensional monogenic commutative `ℂ`-algebra is
`ℂ[X]/(X² − aX − b)`, and its discriminant `Δ = a² + 4b` splits the classification into two
non-isomorphic types: `Δ ≠ 0` gives `ℂ × ℂ` and `Δ = 0` gives the dual numbers.  Generator count,
relation count and rank therefore do not determine the successor law; a frame, polarity or
discriminant is an irreducible extra datum.
-/

namespace HTGeometry.ConstraintRelativity

open Polynomial

/-! ## Unframed rank-one naturality rigidity -/

section RankOne

variable {L : Type*} [AddCommGroup L] [Module ℂ L]

/-- **Rank-one naturality rigidity.**  A bilinear law on `ℂ ⊕ L` that is natural under every
scaling of the line has vanishing product on the line: `L² = 0`. -/
theorem line_mul_eq_zero (mul : (ℂ × L) →ₗ[ℂ] (ℂ × L) →ₗ[ℂ] (ℂ × L))
    (hnat : ∀ lam : ℂ, lam ≠ 0 → ∀ z w : ℂ × L,
      mul (z.1, lam • z.2) (w.1, lam • w.2) = ((mul z w).1, lam • (mul z w).2))
    (x y : L) : mul (0, x) (0, y) = 0 := by
  have hbil : ∀ lam : ℂ, mul (0, lam • x) (0, lam • y) = (lam ^ 2) • mul (0, x) (0, y) := by
    intro lam
    have h1 : ((0 : ℂ), lam • x) = lam • ((0 : ℂ), x) := by ext <;> simp
    have h2 : ((0 : ℂ), lam • y) = lam • ((0 : ℂ), y) := by ext <;> simp
    rw [h1, h2]
    simp only [LinearMap.map_smul, LinearMap.smul_apply, smul_smul, sq]
  have hkey : mul (0, (2 : ℂ) • x) (0, (2 : ℂ) • y)
      = ((mul (0, x) (0, y)).1, (2 : ℂ) • (mul (0, x) (0, y)).2) :=
    hnat 2 two_ne_zero (0, x) (0, y)
  rw [hbil 2] at hkey
  have hfst : (2 : ℂ) ^ 2 * (mul (0, x) (0, y)).1 = (mul (0, x) (0, y)).1 := by
    have h := congrArg Prod.fst hkey
    simpa using h
  have hsnd : ((2 : ℂ) ^ 2) • (mul (0, x) (0, y)).2 = (2 : ℂ) • (mul (0, x) (0, y)).2 := by
    have h := congrArg Prod.snd hkey
    simpa using h
  have h1 : (mul (0, x) (0, y)).1 = 0 := by linear_combination hfst / 3
  have h2 : (mul (0, x) (0, y)).2 = 0 := by
    have hdiff : ((2 : ℂ) ^ 2 - 2) • (mul (0, x) (0, y)).2 = 0 := by
      rw [sub_smul, hsnd, sub_self]
    rw [show (2 : ℂ) ^ 2 - 2 = 2 by ring] at hdiff
    rcases smul_eq_zero.1 hdiff with h | h
    · exact absurd h two_ne_zero
    · exact h
  refine Prod.ext ?_ ?_
  · simpa using h1
  · simpa using h2

/-- The square-zero law on `ℂ ⊕ L`. -/
def dualMul : (ℂ × L) →ₗ[ℂ] (ℂ × L) →ₗ[ℂ] (ℂ × L) :=
  LinearMap.mk₂ ℂ (fun z w => (z.1 * w.1, z.1 • w.2 + w.1 • z.2))
    (fun z z' w => Prod.ext (by simp only [Prod.fst_add]; ring)
      (by simp only [Prod.fst_add, Prod.snd_add, add_smul, smul_add]; abel))
    (fun c z w => Prod.ext (by simp only [Prod.smul_fst, smul_eq_mul]; ring)
      (by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, smul_add, smul_smul]; ring_nf))
    (fun z w w' => Prod.ext (by simp only [Prod.fst_add]; ring)
      (by simp only [Prod.fst_add, Prod.snd_add, add_smul, smul_add]; abel))
    (fun c z w => Prod.ext (by simp only [Prod.smul_fst, smul_eq_mul]; ring)
      (by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, smul_add, smul_smul]; ring_nf))

@[simp]
theorem dualMul_apply (z w : ℂ × L) :
    dualMul z w = (z.1 * w.1, z.1 • w.2 + w.1 • z.2) := rfl

/-- The square-zero law is natural under every scaling of the line, so the rigidity theorem is not
vacuous: it identifies exactly one law. -/
theorem dualMul_natural (lam : ℂ) (z w : ℂ × L) :
    dualMul (z.1, lam • z.2) (w.1, lam • w.2)
      = ((dualMul z w).1, lam • (dualMul z w).2) := by
  simp only [dualMul_apply]
  ext
  · rfl
  · simp only [smul_add]
    rw [smul_comm lam z.1 w.2, smul_comm lam w.1 z.2]

/-- The square-zero law indeed has vanishing product on the line. -/
theorem dualMul_line (x y : L) : dualMul ((0 : ℂ), x) ((0 : ℂ), y) = 0 := by
  simp

end RankOne

/-! ## The framed quadratic classification -/

/-- The framed quadratic law `e² = a e + b`. -/
noncomputable def quadPoly (a b : ℂ) : ℂ[X] := X ^ 2 - C a * X - C b

/-- The framed two-dimensional monogenic algebra `ℂ[e]/(e² − a e − b)`. -/
noncomputable abbrev quadAlgebra (a b : ℂ) : Type := AdjoinRoot (quadPoly a b)

/-- The discriminant `Δ = a² + 4b`. -/
def quadDiscr (a b : ℂ) : ℂ := a ^ 2 + 4 * b

theorem quadPoly_natDegree (a b : ℂ) : (quadPoly a b).natDegree = 2 := by
  unfold quadPoly
  compute_degree!

theorem quadPoly_ne_zero (a b : ℂ) : quadPoly a b ≠ 0 := by
  intro h
  have := quadPoly_natDegree a b
  rw [h] at this
  simp at this

instance quadAlgebra_finiteDimensional (a b : ℂ) : FiniteDimensional ℂ (quadAlgebra a b) :=
  Module.Finite.of_basis (AdjoinRoot.powerBasis (quadPoly_ne_zero a b)).basis

theorem finrank_quadAlgebra (a b : ℂ) : Module.finrank ℂ (quadAlgebra a b) = 2 := by
  rw [(AdjoinRoot.powerBasis (quadPoly_ne_zero a b)).finrank,
    AdjoinRoot.powerBasis_dim, quadPoly_natDegree]

/-- Evaluation of the framed quadratic in any commutative ring. -/
theorem eval₂_quadPoly {S : Type*} [CommRing S] (f : ℂ →+* S) (x : S) (a b : ℂ) :
    (quadPoly a b).eval₂ f x = x ^ 2 - f a * x - f b := by
  simp [quadPoly]

/-- The defining relation of the framed algebra. -/
theorem root_sq (a b : ℂ) :
    (AdjoinRoot.root (quadPoly a b)) ^ 2
      = AdjoinRoot.of (quadPoly a b) a * AdjoinRoot.root (quadPoly a b)
        + AdjoinRoot.of (quadPoly a b) b := by
  have h := AdjoinRoot.eval₂_root (quadPoly a b)
  rw [eval₂_quadPoly] at h
  linear_combination h

/-- The frame is nonzero: it is a basis vector of the power basis. -/
theorem root_ne_zero (a b : ℂ) : AdjoinRoot.root (quadPoly a b) ≠ 0 := by
  set pb := AdjoinRoot.powerBasis (quadPoly_ne_zero a b) with hpb
  have hdim : pb.dim = 2 := by rw [hpb, AdjoinRoot.powerBasis_dim, quadPoly_natDegree]
  have hlt : 1 < pb.dim := by rw [hdim]; omega
  have hne := pb.basis.ne_zero ⟨1, hlt⟩
  rw [PowerBasis.basis_eq_pow] at hne
  have hgen : pb.gen = AdjoinRoot.root (quadPoly a b) := by
    rw [hpb, AdjoinRoot.powerBasis_gen]
  rw [hgen] at hne
  simpa using hne

/-! ### Nondegenerate discriminant: the split type -/

/-- **Split type.**  A nonzero discriminant makes the framed algebra the product `ℂ × ℂ`. -/
theorem exists_algEquiv_prod_of_discr_ne_zero (a b : ℂ) (h : quadDiscr a b ≠ 0) :
    Nonempty (quadAlgebra a b ≃ₐ[ℂ] ℂ × ℂ) := by
  obtain ⟨d, hd⟩ : ∃ d : ℂ, d ^ 2 = a ^ 2 + 4 * b :=
    IsAlgClosed.exists_pow_nat_eq (a ^ 2 + 4 * b) (n := 2) two_pos
  have hd0 : d ≠ 0 := by
    intro hzero
    rw [hzero] at hd
    exact h (by simpa [quadDiscr] using hd.symm)
  set r : ℂ := (a + d) / 2 with hr
  set s : ℂ := (a - d) / 2 with hs
  have hrs : r ≠ s := by
    intro hEq
    exact hd0 (by rw [hr, hs] at hEq; linear_combination hEq)
  have hsub : r - s ≠ 0 := sub_ne_zero.2 hrs
  have hsub' : s - r ≠ 0 := sub_ne_zero.2 (Ne.symm hrs)
  have hroot_r : r ^ 2 - a * r - b = 0 := by rw [hr]; linear_combination hd / 4
  have hroot_s : s ^ 2 - a * s - b = 0 := by rw [hs]; linear_combination hd / 4
  have heval : (quadPoly a b).eval₂ (Algebra.ofId ℂ (ℂ × ℂ)).toRingHom ((r, s) : ℂ × ℂ) = 0 := by
    rw [eval₂_quadPoly]
    refine Prod.ext ?_ ?_
    · simpa [Algebra.ofId_apply] using by linear_combination hroot_r
    · simpa [Algebra.ofId_apply] using by linear_combination hroot_s
  set φ : quadAlgebra a b →ₐ[ℂ] ℂ × ℂ :=
    AdjoinRoot.liftAlgHom (quadPoly a b) (Algebra.ofId ℂ (ℂ × ℂ)) ((r, s) : ℂ × ℂ) heval with hφ
  have hφroot : φ (AdjoinRoot.root (quadPoly a b)) = (r, s) := by
    rw [hφ, AdjoinRoot.liftAlgHom_root]
  have hφof : ∀ c : ℂ, φ (AdjoinRoot.of (quadPoly a b) c) = (c, c) := by
    intro c
    rw [hφ, AdjoinRoot.liftAlgHom_of]
    simp [Algebra.ofId_apply]
  have hsurj : Function.Surjective φ := by
    intro v
    refine ⟨AdjoinRoot.of _ (v.1 / (r - s)) *
        (AdjoinRoot.root (quadPoly a b) - AdjoinRoot.of _ s)
      + AdjoinRoot.of _ (v.2 / (s - r)) *
        (AdjoinRoot.root (quadPoly a b) - AdjoinRoot.of _ r), ?_⟩
    simp only [map_add, map_mul, map_sub, hφroot, hφof]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, Prod.fst_mul, Prod.fst_sub, sub_self, mul_zero, add_zero]
      field_simp
    · simp only [Prod.snd_add, Prod.snd_mul, Prod.snd_sub, sub_self, mul_zero, zero_add]
      field_simp
  have hfr : Module.finrank ℂ (quadAlgebra a b) = Module.finrank ℂ (ℂ × ℂ) := by
    rw [finrank_quadAlgebra]
    simp
  have hinj : Function.Injective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (φ : quadAlgebra a b →ₗ[ℂ] ℂ × ℂ)) hfr).2 hsurj
  exact ⟨AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩⟩

/-! ### Degenerate discriminant: the dual-number type -/

/-- **Degenerate type.**  A vanishing discriminant makes the framed algebra the dual numbers. -/
theorem exists_algEquiv_dual_of_discr_eq_zero (a b : ℂ) (h : quadDiscr a b = 0) :
    Nonempty (quadAlgebra a b ≃ₐ[ℂ] quadAlgebra 0 0) := by
  have hdisc : a ^ 2 + 4 * b = 0 := h
  have hb : b = -((a / 2) ^ 2) := by linear_combination hdisc / 4
  have hι_a : AdjoinRoot.of (quadPoly a b) a
      = 2 * AdjoinRoot.of (quadPoly a b) (a / 2) := by
    rw [← map_ofNat (AdjoinRoot.of (quadPoly a b)) 2, ← map_mul]
    congr 1
    ring
  have hι_b : AdjoinRoot.of (quadPoly a b) b
      = -(AdjoinRoot.of (quadPoly a b) (a / 2)) ^ 2 := by
    rw [← map_pow, ← map_neg]
    congr 1
  have hι₀_a : AdjoinRoot.of (quadPoly (0 : ℂ) 0) a
      = 2 * AdjoinRoot.of (quadPoly (0 : ℂ) 0) (a / 2) := by
    rw [← map_ofNat (AdjoinRoot.of (quadPoly (0 : ℂ) 0)) 2, ← map_mul]
    congr 1
    ring
  have hι₀_b : AdjoinRoot.of (quadPoly (0 : ℂ) 0) b
      = -(AdjoinRoot.of (quadPoly (0 : ℂ) 0) (a / 2)) ^ 2 := by
    rw [← map_pow, ← map_neg]
    congr 1
  have hzeroSq : (AdjoinRoot.root (quadPoly (0 : ℂ) 0)) ^ 2 = 0 := by
    have hz := root_sq (0 : ℂ) 0
    simpa using hz
  have hshiftUp :
      (AdjoinRoot.root (quadPoly (0 : ℂ) 0) + AdjoinRoot.of (quadPoly (0 : ℂ) 0) (a / 2)) ^ 2
        = AdjoinRoot.of (quadPoly (0 : ℂ) 0) a
            * (AdjoinRoot.root (quadPoly (0 : ℂ) 0)
              + AdjoinRoot.of (quadPoly (0 : ℂ) 0) (a / 2))
          + AdjoinRoot.of (quadPoly (0 : ℂ) 0) b := by
    rw [hι₀_a, hι₀_b, add_sq, hzeroSq]
    ring
  have hshiftDown :
      (AdjoinRoot.root (quadPoly a b) - AdjoinRoot.of (quadPoly a b) (a / 2)) ^ 2 = 0 := by
    have hr := root_sq a b
    rw [hι_a, hι_b] at hr
    rw [sub_sq, hr]
    ring
  have heval₁ : (quadPoly a b).eval₂ (Algebra.ofId ℂ (quadAlgebra 0 0)).toRingHom
      (AdjoinRoot.root (quadPoly (0 : ℂ) 0) + AdjoinRoot.of (quadPoly (0 : ℂ) 0) (a / 2)) = 0 := by
    rw [eval₂_quadPoly]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.ofId_apply,
      AdjoinRoot.algebraMap_eq]
    rw [sub_sub, hshiftUp]
    ring
  have heval₂ : (quadPoly (0 : ℂ) 0).eval₂ (Algebra.ofId ℂ (quadAlgebra a b)).toRingHom
      (AdjoinRoot.root (quadPoly a b) - AdjoinRoot.of (quadPoly a b) (a / 2)) = 0 := by
    rw [eval₂_quadPoly]
    simpa using hshiftDown
  set φ : quadAlgebra a b →ₐ[ℂ] quadAlgebra 0 0 :=
    AdjoinRoot.liftAlgHom (quadPoly a b) (Algebra.ofId ℂ (quadAlgebra 0 0)) _ heval₁ with hφ
  set ψ : quadAlgebra 0 0 →ₐ[ℂ] quadAlgebra a b :=
    AdjoinRoot.liftAlgHom (quadPoly (0 : ℂ) 0) (Algebra.ofId ℂ (quadAlgebra a b)) _ heval₂ with hψ
  refine ⟨AlgEquiv.ofAlgHom φ ψ ?_ ?_⟩
  · refine AdjoinRoot.algHom_ext ?_
    rw [AlgHom.comp_apply, hψ, AdjoinRoot.liftAlgHom_root, map_sub, hφ,
      AdjoinRoot.liftAlgHom_root, AdjoinRoot.liftAlgHom_of]
    simp only [Algebra.ofId_apply, AdjoinRoot.algebraMap_eq, AlgHom.coe_id, id_eq]
    ring
  · refine AdjoinRoot.algHom_ext ?_
    rw [AlgHom.comp_apply, hφ, AdjoinRoot.liftAlgHom_root, map_add, hψ,
      AdjoinRoot.liftAlgHom_root, AdjoinRoot.liftAlgHom_of]
    simp only [Algebra.ofId_apply, AdjoinRoot.algebraMap_eq, AlgHom.coe_id, id_eq]
    ring

/-! ### The two types are not isomorphic -/

theorem exists_nilpotent_quadAlgebra_zero :
    ∃ x : quadAlgebra (0 : ℂ) 0, x ≠ 0 ∧ x ^ 2 = 0 := by
  refine ⟨AdjoinRoot.root (quadPoly 0 0), root_ne_zero 0 0, ?_⟩
  have := root_sq (0 : ℂ) 0
  simpa using this

/-- **The two framed types are not isomorphic.**  The degenerate type has a nonzero square-zero
element and the split type is reduced. -/
theorem not_nonempty_algEquiv_dual_prod :
    ¬ Nonempty (quadAlgebra (0 : ℂ) 0 ≃ₐ[ℂ] ℂ × ℂ) := by
  rintro ⟨e⟩
  obtain ⟨x, hx0, hx2⟩ := exists_nilpotent_quadAlgebra_zero
  have hex : (e x) ^ 2 = 0 := by rw [← map_pow, hx2, map_zero]
  have hex0 : e x = 0 := (IsNilpotent.eq_zero ⟨2, hex⟩ : e x = 0)
  exact hx0 (by simpa using e.injective (by simpa using hex0))

/-- **The framing corollary.**  The laws `e² = 0` and `e² = 1` have the same generator and relation
counts and the same rank, yet are not isomorphic: rank data alone cannot determine the successor
law. -/
theorem quadAlgebra_zero_not_algEquiv_one :
    ¬ Nonempty (quadAlgebra (0 : ℂ) 0 ≃ₐ[ℂ] quadAlgebra (0 : ℂ) 1) := by
  rintro ⟨e⟩
  obtain ⟨f⟩ := exists_algEquiv_prod_of_discr_ne_zero (0 : ℂ) 1 (by norm_num [quadDiscr])
  exact not_nonempty_algEquiv_dual_prod ⟨e.trans f⟩

end HTGeometry.ConstraintRelativity
