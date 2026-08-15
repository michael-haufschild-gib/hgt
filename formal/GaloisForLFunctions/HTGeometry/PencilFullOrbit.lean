import GaloisForLFunctions.HTGeometry.PencilOperatorMatroidLaw

/-!
# One pencil source for the whole orbit

The genericity argument produces a source family whose entire countable translation orbit is jointly
hypertranscendental, so one choice of facet sources serves every finite family of operators at once:
a facet together with an integral exponent supported on that facet indexes one orbit member, and
distinct indices have distinct translation classes exactly by the integral independence condition.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial Bottcher
open scoped Classical Differential

noncomputable section

/-! ### Restriction of a joint relation to a subfamily -/

variable {d : ℕ} {ι : Type}

theorem jointlyDirHypertranscendental_comp_injective (w : Fin d → ℂ) {κ : Type}
    (f : ι → (Fin d → ℂ) → ℂ) (φ : κ → ι) (hφ : Function.Injective φ)
    (h : JointlyDirHypertranscendental w f) :
    JointlyDirHypertranscendental w (f ∘ φ) := by
  classical
  rintro ⟨n, Q, hQ, hrel⟩
  have hmapinj : Function.Injective
      (fun v : (Fin d) ⊕ (κ × Fin (n + 1)) => Sum.map id (fun p : κ × Fin (n + 1) =>
        (φ p.1, p.2)) v) := by
    rintro (k | ⟨a, r⟩) (l | ⟨b, t⟩) hv <;> simp only [Sum.map] at hv
    · exact congrArg Sum.inl (Sum.inl_injective hv)
    · exact absurd hv (by simp)
    · exact absurd hv (by simp)
    · obtain ⟨h1, h2⟩ := Prod.mk.injEq .. ▸ Sum.inr_injective hv
      simp only at h1 h2
      rw [hφ h1, h2]
  refine h ⟨n, MvPolynomial.rename
    (fun v : (Fin d) ⊕ (κ × Fin (n + 1)) => Sum.map id (fun p : κ × Fin (n + 1) =>
      (φ p.1, p.2)) v) Q, ?_, fun z => ?_⟩
  · intro hzero
    exact hQ (MvPolynomial.rename_injective _ hmapinj (by rw [hzero, map_zero]))
  · rw [MvPolynomial.eval_rename]
    have hfun : (dirJetPoint w f n z) ∘
        (fun v : (Fin d) ⊕ (κ × Fin (n + 1)) => Sum.map id (fun p : κ × Fin (n + 1) =>
          (φ p.1, p.2)) v) = dirJetPoint w (f ∘ φ) n z := by
      funext v
      cases v with
      | inl k => rfl
      | inr p => rfl
    rw [hfun]
    exact hrel z

/-- An empty family satisfies no algebraic differential relation. -/
theorem jointlyDirHypertranscendental_of_isEmpty (w : Fin d → ℂ) [IsEmpty ι]
    (f : ι → (Fin d → ℂ) → ℂ) : JointlyDirHypertranscendental w f := by
  classical
  rintro ⟨n, Q, hQ, hrel⟩
  haveI : IsEmpty (ι × Fin (n + 1)) := ⟨fun p => IsEmpty.elim ‹IsEmpty ι› p.1⟩
  set e : (Fin d) ⊕ (ι × Fin (n + 1)) ≃ Fin d := Equiv.sumEmpty _ _ with he
  refine hQ ?_
  have hren : MvPolynomial.rename e Q = 0 := by
    refine MvPolynomial.funext fun x => ?_
    rw [MvPolynomial.eval_rename, map_zero]
    have hfun : (x ∘ e) = dirJetPoint w f n x := by
      funext v
      cases v with
      | inl k => rfl
      | inr p => exact IsEmpty.elim ‹IsEmpty (ι × Fin (n + 1))› p
    rw [hfun]
    exact hrel x
  exact MvPolynomial.rename_injective _ e.injective (by rw [hren, map_zero])

/-! ### The full orbit index -/

variable {α : Type} [Fintype α] [DecidableEq α]

/-- One orbit member: a facet together with an integral exponent supported on that facet. -/
def pencilOrbitIndex (facets : Finset (Finset α)) : Type :=
  {p : facets × (α → ℤ) // ∀ v ∉ (p.1 : Finset α), p.2 v = 0}

instance instCountablePencilOrbitIndex (facets : Finset (Finset α)) :
    Countable (pencilOrbitIndex facets) := by
  unfold pencilOrbitIndex
  infer_instance

instance instDecidableEqPencilOrbitIndex (facets : Finset (Finset α)) :
    DecidableEq (pencilOrbitIndex facets) := Classical.decEq _

instance instNonemptyPencilOrbitIndex (facets : Finset (Finset α)) [Nonempty facets] :
    Nonempty (pencilOrbitIndex facets) :=
  ⟨⟨(Classical.arbitrary facets, fun _ => 0), fun _ _ => rfl⟩⟩

/-- The coordinate packet of a Stanley--Reisner Laurent family sits inside the orbit index. -/
def rowIndexToOrbit {facets : Finset (Finset α)} {ι : Type} [Fintype ι]
    (dd : translationSubmonoid (Polynomial ℂ) α)
    (N : ι → MvPolynomial α (Polynomial ℂ) ⧸ stanleyReisnerIdeal (Polynomial ℂ) facets)
    (q : FiniteFinsuppRowIndex (stanleyReisnerLaurentRows dd facets N)) :
    pencilOrbitIndex facets :=
  ⟨(q.1.1, q.1.2), fun _ hv =>
    finiteFinsuppRowIndex_stanleyReisnerLaurentRows_eq_zero dd facets N q hv⟩

theorem rowIndexToOrbit_injective {facets : Finset (Finset α)} {ι : Type} [Fintype ι]
    (dd : translationSubmonoid (Polynomial ℂ) α)
    (N : ι → MvPolynomial α (Polynomial ℂ) ⧸ stanleyReisnerIdeal (Polynomial ℂ) facets) :
    Function.Injective (rowIndexToOrbit dd N) := by
  intro q q' h
  have hval := congrArg (fun p : pencilOrbitIndex facets => p.1) h
  exact Subtype.ext hval

/-! ### One source for the whole orbit -/

set_option maxHeartbeats 8000000 in
/-- **One pencil source serves the whole orbit.**  For facet phases whose steps outside a facet are
periods and whose steps inside a facet are integrally independent modulo the periods, there are
entire facet sources, periodic under every step outside their facet, whose whole translation orbit
satisfies no algebraic differential relation over the coordinates. -/
theorem exists_pencilSource_orbit_jointlyDirHypertranscendental
    (facets : Finset (Finset α))
    (Lf : Finset α → ((Fin d → ℂ) →ₗ[ℂ] ℂ)) (a : α → (Fin d → ℂ)) (w : Fin d → ℂ)
    (hw : ∀ A ∈ facets, Lf A w ≠ 0)
    (houtside : ∀ A ∈ facets, ∀ v ∉ A, Complex.exp (Lf A (a v)) = 1)
    (hinside : ∀ A ∈ facets, ∀ g : α → ℤ,
      Complex.exp (∑ v ∈ A, (g v : ℂ) * Lf A (a v)) = 1 → ∀ v ∈ A, g v = 0) :
    ∃ (Y : facets → (Fin d → ℂ) → ℂ), (∀ A, AnalyticOnNhd ℂ (Y A) Set.univ) ∧
      (∀ (A : facets) (v : α), v ∉ A.1 → ∀ z, Y A (z + a v) = Y A z) ∧
      JointlyDirHypertranscendental w
        (fun p : pencilOrbitIndex facets => fun z => Y p.1.1 (z + pencilShift a p.1.2)) := by
  classical
  rcases isEmpty_or_nonempty (facets : Type) with hemp | hne
  · haveI : IsEmpty (pencilOrbitIndex facets) := ⟨fun p => hemp.elim p.1.1⟩
    exact ⟨fun A => isEmptyElim A, fun A => isEmptyElim A, fun A => isEmptyElim A,
      jointlyDirHypertranscendental_of_isEmpty w _⟩
  · set e := facets.equivFin with he
    have hdist : ∀ p p' : pencilOrbitIndex facets,
        e p.1.1 = e p'.1.1 → p ≠ p' →
        Complex.exp (Lf (p.1.1 : Finset α) (pencilShift a p.1.2)) ≠
          Complex.exp (Lf (p'.1.1 : Finset α) (pencilShift a p'.1.2)) := by
      intro p p' hsrc hne hval
      have hfac : p.1.1 = p'.1.1 := e.injective hsrc
      rw [← hfac] at hval
      have hz : ∀ v ∉ (p.1.1 : Finset α), p.1.2 v = 0 := p.2
      have hz' : ∀ v ∉ (p.1.1 : Finset α), p'.1.2 v = 0 := by
        intro v hv
        exact p'.2 v (by rwa [← hfac])
      have hgout : ∀ v ∉ (p.1.1 : Finset α), p.1.2 v - p'.1.2 v = 0 := by
        intro v hv
        rw [hz v hv, hz' v hv, sub_zero]
      have hsum : ∑ v ∈ (p.1.1 : Finset α),
            ((p.1.2 v - p'.1.2 v : ℤ) : ℂ) * Lf (p.1.1 : Finset α) (a v)
          = Lf (p.1.1 : Finset α) (pencilShift a p.1.2)
            - Lf (p.1.1 : Finset α) (pencilShift a p'.1.2) := by
        rw [map_pencilShift, map_pencilShift, ← Finset.sum_sub_distrib]
        refine (Finset.sum_subset (Finset.subset_univ (p.1.1 : Finset α)) ?_).trans
          (Finset.sum_congr rfl fun v _ => ?_)
        · intro v _ hv
          rw [hgout v hv]
          simp
        · push_cast
          ring
      have hexp1 : Complex.exp (∑ v ∈ (p.1.1 : Finset α),
          ((p.1.2 v - p'.1.2 v : ℤ) : ℂ) * Lf (p.1.1 : Finset α) (a v)) = 1 := by
        rw [hsum, Complex.exp_sub, hval, div_self (Complex.exp_ne_zero _)]
      have hgin := hinside (p.1.1 : Finset α) p.1.1.2 (fun v => p.1.2 v - p'.1.2 v) hexp1
      have hgzero : p.1.2 = p'.1.2 := by
        funext v
        by_cases hv : v ∈ (p.1.1 : Finset α)
        · have h0 : p.1.2 v - p'.1.2 v = 0 := hgin v hv
          omega
        · rw [hz v hv, hz' v hv]
      exact hne (Subtype.ext (Prod.ext hfac hgzero))
    obtain ⟨C, hC⟩ := exists_source_pencil_jointlyDirHypertranscendental (d := d) w
      (fun j : Fin facets.card => Lf (e.symm j).1) (fun j => hw _ (e.symm j).2)
      (fun p : pencilOrbitIndex facets => e p.1.1)
      (fun p => Lf (p.1.1 : Finset α) (pencilShift a p.1.2)) hdist
    have hfam : pencilFam (fun j : Fin facets.card => Lf (e.symm j).1)
          (fun p : pencilOrbitIndex facets => e p.1.1)
          (fun p => Lf (p.1.1 : Finset α) (pencilShift a p.1.2)) C
        = fun p => fun z => pencilFacetMember Lf e C p.1.1 (z + pencilShift a p.1.2) := by
      funext p z
      show jetSeriesFun (boxSeq (C (e p.1.1))) 0
          (Complex.exp (Lf (e.symm (e p.1.1)).1 z
            + Lf (p.1.1 : Finset α) (pencilShift a p.1.2)))
        = jetSeriesFun (boxSeq (C (e p.1.1))) 0
          (Complex.exp (Lf (p.1.1 : Finset α) (z + pencilShift a p.1.2)))
      rw [Equiv.symm_apply_apply, map_add]
    rw [hfam] at hC
    exact ⟨pencilFacetMember Lf e C, analyticOnNhd_pencilFacetMember Lf e C,
      fun A v hv z => pencilFacetMember_add_of_notMem Lf e C a A (houtside A.1 A.2 v hv) z, hC⟩

end

end GaloisForLFunctions.HTGeometry
