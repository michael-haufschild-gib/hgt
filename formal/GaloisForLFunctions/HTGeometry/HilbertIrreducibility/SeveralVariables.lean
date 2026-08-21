import GaloisForLFunctions.HTGeometry.HilbertIrreducibility.Multivariate

/-!
# Hilbert irreducibility for several parameters

Iterating the one-variable specialization of `Multivariate` over all coefficient variables gives a
rational point at which an irreducible polynomial in `ℚ[Y₁,…,Y_m][T]` stays irreducible, keeps its
degree, and avoids the zero set of any prescribed nonzero polynomial.
-/

namespace GaloisForLFunctions.HTGeometry.HilbertIrreducibility

open Polynomial MvPolynomial

/-- The model in which the *first* variable becomes the coefficient variable. -/
noncomputable def killFirst (m : ℕ) :
    MvPolynomial (Fin (m + 1)) ℚ ≃ₐ[ℚ] MvPolynomial (Fin m) (Polynomial ℚ) :=
  (MvPolynomial.renameEquiv ℚ (_root_.finSuccEquiv m)).trans
    (MvPolynomial.optionEquivRight ℚ (Fin m))

theorem killFirst_X_zero (m : ℕ) :
    killFirst m (MvPolynomial.X 0) = MvPolynomial.C Polynomial.X := by
  simp [killFirst, finSuccEquiv_zero]

theorem killFirst_X_succ (m : ℕ) (j : Fin m) :
    killFirst m (MvPolynomial.X j.succ) = MvPolynomial.X j := by
  simp [killFirst, finSuccEquiv_succ]

/-- The model in which the *second* variable becomes the coefficient variable. -/
noncomputable def kill1 (m : ℕ) :
    MvPolynomial (Fin (m + 2)) ℚ ≃ₐ[ℚ] MvPolynomial (Fin (m + 1)) (Polynomial ℚ) :=
  (MvPolynomial.renameEquiv ℚ (Equiv.swap (0 : Fin (m + 2)) 1)).trans (killFirst (m + 1))

theorem one_eq_succ_zero (m : ℕ) : (1 : Fin (m + 2)) = (0 : Fin (m + 1)).succ :=
  (Fin.succ_zero_eq_one).symm

theorem kill1_X_zero (m : ℕ) :
    kill1 m (MvPolynomial.X 0) = MvPolynomial.X 0 := by
  have h1 : (Equiv.swap (0 : Fin (m + 2)) 1) 0 = 1 := Equiv.swap_apply_left 0 1
  rw [kill1]
  simp only [AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X, h1]
  rw [one_eq_succ_zero, killFirst_X_succ]

theorem kill1_X_one (m : ℕ) :
    kill1 m (MvPolynomial.X 1) = MvPolynomial.C Polynomial.X := by
  have h1 : (Equiv.swap (0 : Fin (m + 2)) 1) 1 = 0 := Equiv.swap_apply_right 0 1
  rw [kill1]
  simp only [AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X, h1,
    killFirst_X_zero]

theorem kill1_X_succ_succ (m : ℕ) (j : Fin m) :
    kill1 m (MvPolynomial.X j.succ.succ) = MvPolynomial.X j.succ := by
  have hne0 : (j.succ.succ : Fin (m + 2)) ≠ 0 := Fin.succ_ne_zero _
  have hne1 : (j.succ.succ : Fin (m + 2)) ≠ 1 := by
    rw [one_eq_succ_zero]
    exact fun h => Fin.succ_ne_zero j (Fin.succ_injective _ h)
  have h1 : (Equiv.swap (0 : Fin (m + 2)) 1) j.succ.succ = j.succ.succ :=
    Equiv.swap_apply_of_ne_of_ne hne0 hne1
  rw [kill1]
  simp only [AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X, h1,
    killFirst_X_succ]

/-- Substitution of a rational constant for the first variable. -/
noncomputable def spec0 {m : ℕ} (c : ℚ) :
    MvPolynomial (Fin (m + 1)) ℚ →ₐ[ℚ] MvPolynomial (Fin m) ℚ :=
  MvPolynomial.aeval (Fin.cases (MvPolynomial.C c) (fun j : Fin m => MvPolynomial.X j))

@[simp] theorem spec0_X_zero {m : ℕ} (c : ℚ) :
    spec0 (m := m) c (MvPolynomial.X 0) = MvPolynomial.C c := by
  simp [spec0]

@[simp] theorem spec0_X_succ {m : ℕ} (c : ℚ) (j : Fin m) :
    spec0 c (MvPolynomial.X j.succ) = MvPolynomial.X j := by
  simp [spec0]

theorem mapAlgHom_aeval_eq {m : ℕ} (c : ℚ) (p : MvPolynomial (Fin m) (Polynomial ℚ)) :
    MvPolynomial.mapAlgHom (Polynomial.aeval c) p
      = MvPolynomial.map (Polynomial.evalRingHom c) p := rfl

/-- `spec0` is the specialization of the coefficient variable in the `killFirst` model. -/
theorem spec0_eq {m : ℕ} (c : ℚ) (p : MvPolynomial (Fin (m + 1)) ℚ) :
    spec0 c p = MvPolynomial.map (Polynomial.evalRingHom c) (killFirst m p) := by
  have key : (spec0 (m := m) c)
      = (MvPolynomial.mapAlgHom (Polynomial.aeval c)).comp (killFirst m).toAlgHom := by
    refine MvPolynomial.algHom_ext fun i => ?_
    refine Fin.cases ?_ ?_ i
    · simp [killFirst_X_zero]
    · intro j
      simp [killFirst_X_succ]
  rw [key]
  rfl

theorem mvFinSuccEquiv_symm_X {n : ℕ} :
    (MvPolynomial.finSuccEquiv ℚ n).symm Polynomial.X = MvPolynomial.X 0 := by
  rw [← MvPolynomial.finSuccEquiv_X_zero (R := ℚ) (n := n), AlgEquiv.symm_apply_apply]

theorem mvFinSuccEquiv_symm_C_X {n : ℕ} (j : Fin n) :
    (MvPolynomial.finSuccEquiv ℚ n).symm (Polynomial.C (MvPolynomial.X j))
      = MvPolynomial.X j.succ := by
  rw [← MvPolynomial.finSuccEquiv_X_succ (R := ℚ) (n := n) (j := j), AlgEquiv.symm_apply_apply]

theorem mvFinSuccEquiv_symm_C_C {n : ℕ} (c : ℚ) :
    (MvPolynomial.finSuccEquiv ℚ n).symm (Polynomial.C (MvPolynomial.C c))
      = MvPolynomial.C c := by
  have h : (MvPolynomial.finSuccEquiv ℚ n) (MvPolynomial.C c)
      = Polynomial.C (MvPolynomial.C c) := by
    rw [← MvPolynomial.algebraMap_eq, AlgEquiv.commutes]
    simp [Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
  rw [← h, AlgEquiv.symm_apply_apply]

/-- Specializing the coefficient variable of the `kill1` model is the same as specializing the
first coefficient variable of the two-level model. -/
theorem step_emb {m : ℕ} (c : ℚ) (G : Polynomial (MvPolynomial (Fin (m + 1)) ℚ)) :
    MvPolynomial.map (Polynomial.evalRingHom c)
        (kill1 m ((MvPolynomial.finSuccEquiv ℚ (m + 1)).symm G))
      = (MvPolynomial.finSuccEquiv ℚ m).symm (Polynomial.map (spec0 c).toRingHom G) := by
  have key :
      ((MvPolynomial.mapAlgHom (Polynomial.aeval c)).comp
          ((kill1 m).toAlgHom.comp (MvPolynomial.finSuccEquiv ℚ (m + 1)).symm.toAlgHom))
        = (MvPolynomial.finSuccEquiv ℚ m).symm.toAlgHom.comp
            (Polynomial.mapAlgHom (spec0 c)) := by
    refine Polynomial.algHom_ext' ?_ ?_
    · refine MvPolynomial.algHom_ext fun i => ?_
      refine Fin.cases ?_ ?_ i
      · simp [Polynomial.coe_mapAlgHom, MvPolynomial.mapAlgHom_apply, mvFinSuccEquiv_symm_C_X,
          kill1_X_one, spec0_X_zero, mvFinSuccEquiv_symm_C_C]
      · intro j
        simp [Polynomial.coe_mapAlgHom, MvPolynomial.mapAlgHom_apply, mvFinSuccEquiv_symm_C_X,
          kill1_X_succ_succ, spec0_X_succ]
    · simp [Polynomial.coe_mapAlgHom, MvPolynomial.mapAlgHom_apply, mvFinSuccEquiv_symm_X,
        kill1_X_zero]
  have h := congrArg (fun F => F G) key
  simpa [mapAlgHom_aeval_eq] using h

/-- The set of specialization values killing a nonzero polynomial is finite. -/
theorem finite_spec0_zero {m : ℕ} {g : MvPolynomial (Fin (m + 1)) ℚ} (hg : g ≠ 0) :
    {c : ℚ | spec0 c g = 0}.Finite := by
  classical
  have hk : killFirst m g ≠ 0 := by
    intro h
    apply hg
    have := congrArg (killFirst m).symm h
    simpa using this
  obtain ⟨a, ha⟩ : ∃ a, (killFirst m g).coeff a ≠ 0 := by
    by_contra hc
    refine hk (MvPolynomial.ext _ 0 fun a => ?_)
    rw [MvPolynomial.coeff_zero]
    exact not_not.mp (fun h => hc ⟨a, h⟩)
  refine Set.Finite.subset (Polynomial.finite_setOf_isRoot ha) ?_
  intro c hc
  have h0 : MvPolynomial.map (Polynomial.evalRingHom c) (killFirst m g) = 0 := by
    rw [← spec0_eq]
    exact hc
  have h1 := congrArg (fun p => MvPolynomial.coeff a p) h0
  simpa [MvPolynomial.coeff_map, Polynomial.IsRoot] using h1

/-- **Hilbert irreducibility in several parameters.**  An irreducible polynomial in
`ℚ[Y₁,…,Y_m][T]` of positive `T`-degree stays irreducible, and keeps its degree, at a rational
point avoiding the zero locus of any prescribed nonzero polynomial. -/
theorem hilbert_several : ∀ (m : ℕ) (G : Polynomial (MvPolynomial (Fin m) ℚ))
    (g : MvPolynomial (Fin m) ℚ), Irreducible G → 1 ≤ G.natDegree → g ≠ 0 →
      ∃ y : Fin m → ℚ, MvPolynomial.eval y g ≠ 0 ∧
        Irreducible (G.map (MvPolynomial.eval y)) ∧
        (G.map (MvPolynomial.eval y)).natDegree = G.natDegree := by
  intro m
  induction m with
  | zero =>
      intro G g hG hdeg hg
      have heq : (MvPolynomial.eval (Fin.elim0 : Fin 0 → ℚ))
          = (MvPolynomial.isEmptyAlgEquiv ℚ (Fin 0)).toRingEquiv.toRingHom := by
        refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => i.elim0)
        simp [MvPolynomial.coeff_C]
      refine ⟨Fin.elim0, ?_, ?_, ?_⟩
      · rw [heq]
        exact fun h => hg ((MvPolynomial.isEmptyAlgEquiv ℚ (Fin 0)).toRingEquiv.injective
          (by simpa using h))
      · rw [heq]
        have hmap : Polynomial.map
            ((MvPolynomial.isEmptyAlgEquiv ℚ (Fin 0)).toRingEquiv.toRingHom) G
              = Polynomial.mapEquiv (MvPolynomial.isEmptyAlgEquiv ℚ (Fin 0)).toRingEquiv G := rfl
        rw [hmap]
        exact (MulEquiv.irreducible_iff
          (Polynomial.mapEquiv (MvPolynomial.isEmptyAlgEquiv ℚ (Fin 0)).toRingEquiv)).mpr hG
      · rw [heq]
        exact Polynomial.natDegree_map_eq_of_injective
          (MvPolynomial.isEmptyAlgEquiv ℚ (Fin 0)).toRingEquiv.injective G
  | succ m ih =>
      intro G g hG hdeg hg
      have hGne : G ≠ 0 := hG.ne_zero
      obtain ⟨f, hf⟩ : ∃ f : MvPolynomial (Fin (m + 1)) (Polynomial ℚ),
          f = kill1 m ((MvPolynomial.finSuccEquiv ℚ (m + 1)).symm G) := ⟨_, rfl⟩
      have hfirr : Irreducible f := by
        rw [hf]
        exact (MulEquiv.irreducible_iff (kill1 m)).mpr
          ((MulEquiv.irreducible_iff (MvPolynomial.finSuccEquiv ℚ (m + 1)).symm).mpr hG)
      have hftd : 0 < f.totalDegree := by
        rcases Nat.eq_zero_or_pos f.totalDegree with h0 | h
        · exfalso
          obtain ⟨q, hq⟩ : ∃ q : Polynomial ℚ, f = MvPolynomial.C q :=
            ⟨MvPolynomial.coeff 0 f, MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp h0⟩
          have h1 : (kill1 m).symm (MvPolynomial.C Polynomial.X)
              = MvPolynomial.X (1 : Fin (m + 2)) := by
            rw [← kill1_X_one m, AlgEquiv.symm_apply_apply]
          have h2 : (MvPolynomial.finSuccEquiv ℚ (m + 1)) (MvPolynomial.X (1 : Fin (m + 2)))
              = Polynomial.C (MvPolynomial.X (0 : Fin (m + 1))) := by
            rw [one_eq_succ_zero, MvPolynomial.finSuccEquiv_X_succ]
          have hXi : ∀ r : Polynomial ℚ,
              (MvPolynomial.finSuccEquiv ℚ (m + 1)) ((kill1 m).symm (MvPolynomial.C r))
                = Polynomial.C (Polynomial.aeval (MvPolynomial.X (0 : Fin (m + 1))) r) := by
            intro r
            have key : ((MvPolynomial.finSuccEquiv ℚ (m + 1)).toAlgHom.comp
                  ((kill1 m).symm.toAlgHom.comp (IsScalarTower.toAlgHom ℚ (Polynomial ℚ)
                    (MvPolynomial (Fin (m + 1)) (Polynomial ℚ)))))
                = Polynomial.CAlgHom.comp
                    (Polynomial.aeval (MvPolynomial.X (0 : Fin (m + 1)))) := by
              refine Polynomial.algHom_ext ?_
              simp [MvPolynomial.algebraMap_eq, h1, h2]
            have hr := congrArg (fun F => F r) key
            simpa [MvPolynomial.algebraMap_eq] using hr
          have hGval : G = Polynomial.C
              (Polynomial.aeval (MvPolynomial.X (0 : Fin (m + 1))) q) := by
            have hsymm : (kill1 m).symm f = (MvPolynomial.finSuccEquiv ℚ (m + 1)).symm G := by
              rw [hf, AlgEquiv.symm_apply_apply]
            rw [← hXi q, ← hq, hsymm, AlgEquiv.apply_symm_apply]
          rw [hGval, Polynomial.natDegree_C] at hdeg
          omega
        · exact h
      have hinf := exists_infinite_specialisation hfirr hftd
      have hfin1 : {c : ℚ | spec0 c g = 0}.Finite := finite_spec0_zero hg
      have hfin2 : {c : ℚ | spec0 c G.leadingCoeff = 0}.Finite :=
        finite_spec0_zero (Polynomial.leadingCoeff_ne_zero.mpr hGne)
      obtain ⟨c, ⟨⟨hc, hc1⟩, hc2⟩⟩ := ((hinf.sdiff hfin1).sdiff hfin2).nonempty
      have hc1' : spec0 c g ≠ 0 := hc1
      have hc2' : spec0 c G.leadingCoeff ≠ 0 := hc2
      have hdeg' : (G.map (spec0 c).toRingHom).natDegree = G.natDegree :=
        Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ hc2'
      have hGirr' : Irreducible (G.map (spec0 c).toRingHom) := by
        have h1 : Irreducible
            ((MvPolynomial.finSuccEquiv ℚ m).symm (G.map (spec0 c).toRingHom)) := by
          rw [← step_emb c G, ← hf]
          exact hc
        exact (MulEquiv.irreducible_iff (MvPolynomial.finSuccEquiv ℚ m).symm).mp h1
      obtain ⟨y', hy'g, hy'irr, hy'deg⟩ :=
        ih (G.map (spec0 c).toRingHom) (spec0 c g) hGirr' (by omega) hc1'
      have heval : (MvPolynomial.eval (Fin.cons c y') : MvPolynomial (Fin (m + 1)) ℚ →+* ℚ)
          = (MvPolynomial.eval y').comp (spec0 c).toRingHom := by
        refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
        · simp
        · refine Fin.cases ?_ ?_ i
          · simp
          · intro j
            simp
      refine ⟨Fin.cons c y', ?_, ?_, ?_⟩
      · rw [show MvPolynomial.eval (Fin.cons c y') g
            = (MvPolynomial.eval y').comp (spec0 c).toRingHom g from by rw [heval]]
        exact hy'g
      · rw [heval, ← Polynomial.map_map]
        exact hy'irr
      · rw [heval, ← Polynomial.map_map, hy'deg, hdeg']

/-- **Hilbert irreducibility in several parameters**, in the form consumed downstream. -/
theorem hilbert_multivariate {m : ℕ} {G : Polynomial (MvPolynomial (Fin m) ℚ)}
    (hG : Irreducible G) (hdeg : 1 ≤ G.natDegree) {g : MvPolynomial (Fin m) ℚ} (hg : g ≠ 0) :
    ∃ y : Fin m → ℚ, MvPolynomial.eval y g ≠ 0 ∧ Irreducible (G.map (MvPolynomial.eval y)) ∧
      (G.map (MvPolynomial.eval y)).natDegree = G.natDegree :=
  hilbert_several m G g hG hdeg hg

end GaloisForLFunctions.HTGeometry.HilbertIrreducibility


