import GaloisForLFunctions.HTGeometry.OrbitBaireCountable

/-!
# Restricting a several-variable relation to a line

A joint algebraic differential relation over `ℂ(z₁,…,z_d)` with the constant derivation `D_w`
restricts, along the line `z = z₀ + s·w`, to a joint relation in one variable: the coordinates become
affine functions of `s` and the directional jets become the ordinary jets of the restricted family.

The restricted relation is nonzero for a suitable `z₀`, because a polynomial whose specialization in
the coordinate variables vanishes at every point vanishes.  So joint hypertranscendence on every line
in the direction `w` is joint hypertranscendence over `ℂ(z₁,…,z_d)` for `D_w`.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {d : ℕ} {ι : Type}

/-- The jet point of a family on `ℂ^d` for the constant directional derivation `D_w`. -/
def dirJetPoint (w : Fin d → ℂ) (f : ι → (Fin d → ℂ) → ℂ) (n : ℕ) (z : Fin d → ℂ) :
    (Fin d) ⊕ (ι × Fin (n + 1)) → ℂ :=
  Sum.elim (fun k => z k) fun p => iteratedDeriv (p.2 : ℕ) (fun s : ℂ => f p.1 (z + s • w)) 0

/-- **Jointly differentially algebraic over `ℂ(z₁,…,z_d)` for `D_w`.** -/
def JointlyDirDifferentiallyAlgebraic (w : Fin d → ℂ) (f : ι → (Fin d → ℂ) → ℂ) : Prop :=
  ∃ (n : ℕ) (Q : MvPolynomial ((Fin d) ⊕ (ι × Fin (n + 1))) ℂ), Q ≠ 0 ∧
    ∀ z : Fin d → ℂ, MvPolynomial.eval (dirJetPoint w f n z) Q = 0

/-- **Jointly hypertranscendental over `ℂ(z₁,…,z_d)` for `D_w`.** -/
def JointlyDirHypertranscendental (w : Fin d → ℂ) (f : ι → (Fin d → ℂ) → ℂ) : Prop :=
  ¬ JointlyDirDifferentiallyAlgebraic w f

/-- The restriction of the family to the line through `z₀` in the direction `w`. -/
def lineRestrict (w : Fin d → ℂ) (f : ι → (Fin d → ℂ) → ℂ) (z₀ : Fin d → ℂ) : ι → ℂ → ℂ :=
  fun i s => f i (z₀ + s • w)

/-- **The directional jets along a line are the ordinary jets of the restriction.** -/
theorem dirJetPoint_line (w : Fin d → ℂ) (f : ι → (Fin d → ℂ) → ℂ) (n : ℕ) (z₀ : Fin d → ℂ)
    (s : ℂ) :
    dirJetPoint w f n (z₀ + s • w) =
      Sum.elim (fun k => z₀ k + s * w k)
        fun p => famJetPoint (lineRestrict w f z₀) n s (some p) := by
  funext v
  cases v with
  | inl k =>
      show (z₀ + s • w) k = z₀ k + s * w k
      simp
  | inr p =>
      show iteratedDeriv (p.2 : ℕ) (fun s' : ℂ => f p.1 (z₀ + s • w + s' • w)) 0 =
        iteratedDeriv (p.2 : ℕ) (lineRestrict w f z₀ p.1) s
      have harg : (fun s' : ℂ => f p.1 (z₀ + s • w + s' • w)) =
          fun s' : ℂ => lineRestrict w f z₀ p.1 (s + s') := by
        funext s'
        rw [lineRestrict]
        congr 1
        funext k
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [harg, iteratedDeriv_comp_const_add (p.2 : ℕ) (lineRestrict w f z₀ p.1) s]
      simp

/-- The substitution restricting a relation to a line. -/
def lineSubst (w z₀ : Fin d → ℂ) (ι : Type) (n : ℕ) :
    ((Fin d) ⊕ (ι × Fin (n + 1))) → MvPolynomial (Option (ι × Fin (n + 1))) ℂ :=
  Sum.elim (fun k => MvPolynomial.C (z₀ k) + MvPolynomial.C (w k) * MvPolynomial.X none)
    fun p => MvPolynomial.X (some p)

/-- The substitution specializing the coordinate variables to a point. -/
def pointSubst (z₀ : Fin d → ℂ) (ι : Type) (n : ℕ) :
    ((Fin d) ⊕ (ι × Fin (n + 1))) → MvPolynomial (ι × Fin (n + 1)) ℂ :=
  Sum.elim (fun k => MvPolynomial.C (z₀ k)) fun p => MvPolynomial.X p

/-- **A polynomial whose coordinate specialization vanishes at every point is zero.** -/
theorem exists_pointSubst_ne_zero {n : ℕ}
    {Q : MvPolynomial ((Fin d) ⊕ (ι × Fin (n + 1))) ℂ} (hQ : Q ≠ 0) :
    ∃ z₀ : Fin d → ℂ, MvPolynomial.bind₁ (pointSubst z₀ ι n) Q ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  refine hQ (MvPolynomial.funext fun V => ?_)
  have hspec := hcon fun k => V (Sum.inl k)
  have hEq : MvPolynomial.eval (fun p => V (Sum.inr p))
        (MvPolynomial.bind₁ (pointSubst (fun k => V (Sum.inl k)) ι n) Q) =
      MvPolynomial.eval
        (fun v => MvPolynomial.eval (fun p => V (Sum.inr p))
          (pointSubst (fun k => V (Sum.inl k)) ι n v)) Q :=
    eval₂Hom_bind₁ (RingHom.id ℂ) (fun p => V (Sum.inr p)) _ Q
  have hfun : (fun v => MvPolynomial.eval (fun p => V (Sum.inr p))
      (pointSubst (fun k => V (Sum.inl k)) ι n v)) = V := by
    funext v
    cases v with
    | inl k => simp [pointSubst]
    | inr p => simp [pointSubst]
  rw [hfun] at hEq
  rw [hspec, map_zero] at hEq
  rw [map_zero]
  exact hEq.symm

/-- **The line restriction of a nonzero relation is nonzero, for a suitable base point.** -/
theorem exists_lineSubst_ne_zero (w : Fin d → ℂ) {n : ℕ}
    {Q : MvPolynomial ((Fin d) ⊕ (ι × Fin (n + 1))) ℂ} (hQ : Q ≠ 0) :
    ∃ z₀ : Fin d → ℂ, MvPolynomial.bind₁ (lineSubst w z₀ ι n) Q ≠ 0 := by
  classical
  obtain ⟨z₀, hz₀⟩ := exists_pointSubst_ne_zero (ι := ι) hQ
  refine ⟨z₀, fun h => hz₀ ?_⟩
  have hfun : (fun v => MvPolynomial.bind₁
      (fun u : Option (ι × Fin (n + 1)) => u.elim (0 : MvPolynomial (ι × Fin (n + 1)) ℂ)
        fun p => MvPolynomial.X p) (lineSubst w z₀ ι n v)) = pointSubst z₀ ι n := by
    funext v
    cases v with
    | inl k => simp [lineSubst, pointSubst]
    | inr p => simp [lineSubst, pointSubst]
  have hkey := MvPolynomial.bind₁_bind₁ (lineSubst w z₀ ι n)
    (fun u : Option (ι × Fin (n + 1)) => u.elim (0 : MvPolynomial (ι × Fin (n + 1)) ℂ)
      fun p => MvPolynomial.X p) Q
  rw [hfun] at hkey
  rw [← hkey, h, map_zero]

/-- **Joint hypertranscendence on every line in the direction `w` is joint hypertranscendence over
`ℂ(z₁,…,z_d)` for `D_w`.** -/
theorem jointlyDirHypertranscendental_of_lines (w : Fin d → ℂ) (f : ι → (Fin d → ℂ) → ℂ)
    (h : ∀ z₀ : Fin d → ℂ, JointlyHypertranscendental (lineRestrict w f z₀)) :
    JointlyDirHypertranscendental w f := by
  rintro ⟨n, Q, hQ, hrel⟩
  obtain ⟨z₀, hz₀⟩ := exists_lineSubst_ne_zero (ι := ι) w hQ
  refine h z₀ ⟨n, MvPolynomial.bind₁ (lineSubst w z₀ ι n) Q, hz₀, fun s => ?_⟩
  have hEq : MvPolynomial.eval (famJetPoint (lineRestrict w f z₀) n s)
        (MvPolynomial.bind₁ (lineSubst w z₀ ι n) Q) =
      MvPolynomial.eval
        (fun v => MvPolynomial.eval (famJetPoint (lineRestrict w f z₀) n s)
          (lineSubst w z₀ ι n v)) Q :=
    eval₂Hom_bind₁ (RingHom.id ℂ) (famJetPoint (lineRestrict w f z₀) n s) _ Q
  have hfun : (fun v => MvPolynomial.eval (famJetPoint (lineRestrict w f z₀) n s)
      (lineSubst w z₀ ι n v)) = dirJetPoint w f n (z₀ + s • w) := by
    rw [dirJetPoint_line]
    funext v
    cases v with
    | inl k =>
        simp only [lineSubst, Sum.elim_inl, map_add, map_mul, MvPolynomial.eval_C,
          MvPolynomial.eval_X, Sum.elim_inl]
        rw [famJetPoint_none]
        ring
    | inr p => simp [lineSubst]
  rw [hfun] at hEq
  rw [hEq]
  exact hrel _

/-! ### Restricting to lines through a prescribed box of base points -/

/-- **A polynomial whose coordinate specialization vanishes on a box with infinite sides is
zero.** -/
theorem exists_pointSubst_ne_zero_mem {n : ℕ}
    {Q : MvPolynomial ((Fin d) ⊕ (ι × Fin (n + 1))) ℂ} (hQ : Q ≠ 0)
    (S : Fin d → Set ℂ) (hS : ∀ k, (S k).Infinite) :
    ∃ z₀ ∈ Set.pi Set.univ S, MvPolynomial.bind₁ (pointSubst z₀ ι n) Q ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  refine hQ (MvPolynomial.funext_set (p := Q) (q := 0)
    (Sum.elim S fun _ => (Set.univ : Set ℂ)) ?_ ?_)
  · intro v
    cases v with
    | inl k => exact hS k
    | inr p => exact Set.infinite_univ
  · intro V hV
    have hVmem : (fun k => V (Sum.inl k)) ∈ Set.pi Set.univ S := by
      intro k _
      exact hV (Sum.inl k) (Set.mem_univ _)
    have hspec := hcon (fun k => V (Sum.inl k)) hVmem
    have hEq : MvPolynomial.eval (fun p => V (Sum.inr p))
          (MvPolynomial.bind₁ (pointSubst (fun k => V (Sum.inl k)) ι n) Q) =
        MvPolynomial.eval
          (fun v => MvPolynomial.eval (fun p => V (Sum.inr p))
            (pointSubst (fun k => V (Sum.inl k)) ι n v)) Q :=
      eval₂Hom_bind₁ (RingHom.id ℂ) (fun p => V (Sum.inr p)) _ Q
    have hfun : (fun v => MvPolynomial.eval (fun p => V (Sum.inr p))
        (pointSubst (fun k => V (Sum.inl k)) ι n v)) = V := by
      funext v
      cases v with
      | inl k => simp [pointSubst]
      | inr p => simp [pointSubst]
    rw [hfun, hspec, map_zero] at hEq
    rw [map_zero]
    exact hEq.symm

theorem exists_lineSubst_ne_zero_mem (w : Fin d → ℂ) {n : ℕ}
    {Q : MvPolynomial ((Fin d) ⊕ (ι × Fin (n + 1))) ℂ} (hQ : Q ≠ 0)
    (S : Fin d → Set ℂ) (hS : ∀ k, (S k).Infinite) :
    ∃ z₀ ∈ Set.pi Set.univ S, MvPolynomial.bind₁ (lineSubst w z₀ ι n) Q ≠ 0 := by
  classical
  obtain ⟨z₀, hz₀mem, hz₀⟩ := exists_pointSubst_ne_zero_mem (ι := ι) hQ S hS
  refine ⟨z₀, hz₀mem, fun h => hz₀ ?_⟩
  have hfun : (fun v => MvPolynomial.bind₁
      (fun u : Option (ι × Fin (n + 1)) => u.elim (0 : MvPolynomial (ι × Fin (n + 1)) ℂ)
        fun p => MvPolynomial.X p) (lineSubst w z₀ ι n v)) = pointSubst z₀ ι n := by
    funext v
    cases v with
    | inl k => simp [lineSubst, pointSubst]
    | inr p => simp [lineSubst, pointSubst]
  have hkey := MvPolynomial.bind₁_bind₁ (lineSubst w z₀ ι n)
    (fun u : Option (ι × Fin (n + 1)) => u.elim (0 : MvPolynomial (ι × Fin (n + 1)) ℂ)
      fun p => MvPolynomial.X p) Q
  rw [hfun] at hkey
  rw [← hkey, h, map_zero]

/-- **Joint hypertranscendence on the lines through a box with infinite sides suffices.** -/
theorem jointlyDirHypertranscendental_of_lines_mem (w : Fin d → ℂ) (f : ι → (Fin d → ℂ) → ℂ)
    (S : Fin d → Set ℂ) (hS : ∀ k, (S k).Infinite)
    (h : ∀ z₀ ∈ Set.pi Set.univ S, JointlyHypertranscendental (lineRestrict w f z₀)) :
    JointlyDirHypertranscendental w f := by
  rintro ⟨n, Q, hQ, hrel⟩
  obtain ⟨z₀, hz₀mem, hz₀⟩ := exists_lineSubst_ne_zero_mem (ι := ι) w hQ S hS
  refine h z₀ hz₀mem ⟨n, MvPolynomial.bind₁ (lineSubst w z₀ ι n) Q, hz₀, fun s => ?_⟩
  have hEq : MvPolynomial.eval (famJetPoint (lineRestrict w f z₀) n s)
        (MvPolynomial.bind₁ (lineSubst w z₀ ι n) Q) =
      MvPolynomial.eval
        (fun v => MvPolynomial.eval (famJetPoint (lineRestrict w f z₀) n s)
          (lineSubst w z₀ ι n v)) Q :=
    eval₂Hom_bind₁ (RingHom.id ℂ) (famJetPoint (lineRestrict w f z₀) n s) _ Q
  have hfun : (fun v => MvPolynomial.eval (famJetPoint (lineRestrict w f z₀) n s)
      (lineSubst w z₀ ι n v)) = dirJetPoint w f n (z₀ + s • w) := by
    rw [dirJetPoint_line]
    funext v
    cases v with
    | inl k =>
        simp only [lineSubst, Sum.elim_inl, map_add, map_mul, MvPolynomial.eval_C,
          MvPolynomial.eval_X, Sum.elim_inl]
        rw [famJetPoint_none]
        ring
    | inr p => simp [lineSubst]
  rw [hfun] at hEq
  rw [hEq]
  exact hrel _

/-! ### Reindexing a jointly hypertranscendental family -/

/-- **An injective reindexing of a jointly hypertranscendental family is jointly
hypertranscendental.** -/
theorem jointlyHypertranscendental_comp_injective {κ : Type} (f : ι → ℂ → ℂ) (φ : κ → ι)
    (hφ : Function.Injective φ) (h : JointlyHypertranscendental f) :
    JointlyHypertranscendental (f ∘ φ) := by
  classical
  rintro ⟨n, Q, hQ, hrel⟩
  have hmapinj : Function.Injective
      (fun v : Option (κ × Fin (n + 1)) => v.map fun p => (φ p.1, p.2)) := by
    rintro (_ | ⟨a, r⟩) (_ | ⟨b, t⟩) hv <;> simp only [Option.map] at hv
    · rfl
    · exact absurd hv (by simp)
    · exact absurd hv (by simp)
    · obtain ⟨h1, h2⟩ := Prod.mk.injEq .. ▸ Option.some_injective _ hv
      rw [hφ h1, h2]
  refine h ⟨n, MvPolynomial.rename
    (fun v : Option (κ × Fin (n + 1)) => v.map fun p => (φ p.1, p.2)) Q, ?_, fun z => ?_⟩
  · intro hzero
    exact hQ (MvPolynomial.rename_injective _ hmapinj (by rw [hzero, map_zero]))
  · rw [MvPolynomial.eval_rename]
    have hfun : (famJetPoint f n z) ∘
        (fun v : Option (κ × Fin (n + 1)) => v.map fun p => (φ p.1, p.2)) =
        famJetPoint (f ∘ φ) n z := by
      funext v
      cases v with
      | none => rfl
      | some p => rfl
    rw [hfun]
    exact hrel z

end

end GaloisForLFunctions.HTGeometry
