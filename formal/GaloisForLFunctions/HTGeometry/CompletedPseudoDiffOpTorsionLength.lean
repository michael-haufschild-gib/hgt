import GaloisForLFunctions.HTGeometry.CompletedPseudoDiffOpResidueLength

/-!
# Finite length of uniformizer-torsion modules

The layer between two commensurable integral lattices is killed by a uniformizer power, so the
degree of an invariant subspace is a difference of finite numbers exactly when such modules have
finite length.  This leaf proves that.

The noncommutative point is that multiplication by a uniformizer power is not `O`-linear but
`O`-semilinear: `π^k a = (π^k a π^{-k}) π^k`, with the conjugate again integral.  That identity is
isolated as `DiffOp.uniformizerInteger_pow_mul`, together with the bridge
`DiffOp.coe_uniformizerInteger_pow` identifying the ring power with the unit power.  With it the
annihilator of a uniformizer power is a genuine submodule (`DiffOp.uniformizerTorsion`).

```text
DiffOp.length_ne_top_of_fg_of_uniformizer_smul_eq_zero       killed by π
DiffOp.length_ne_top_of_fg_of_uniformizer_pow_smul_eq_zero   killed by πᵏ
```

The second is an induction on `k`.  Splitting a finitely generated `A` along the submodule generated
by `π·(generators)` gives an exact sequence: the sub-object is finitely generated and killed by
`π^{k}`, so the induction hypothesis applies, while the quotient is finitely generated and killed by
`π`, so the residue-length bound applies.  Semilinearity is what makes the sub-object the *span of
the scaled generators* rather than the naive image.
-/

open scoped Differential BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K : Type*} [Field K] [Differential K]

/-- The uniformizer power inside the valuation ring is the uniformizer unit power. -/
theorem DiffOp.coe_uniformizerInteger_pow (k : ℕ) :
    ((DiffOp.uniformizerInteger (K := K) ^ k :
        DiffOp.CompletedPseudoDiffOpInteger (K := K)) : DiffOp.CompletedPseudoDiffOp K) =
      ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ ((k : ℕ) : ℤ) :
        (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ]
      show ((DiffOp.uniformizerInteger (K := K) ^ k :
        DiffOp.CompletedPseudoDiffOpInteger (K := K)) : DiffOp.CompletedPseudoDiffOp K) *
        ((DiffOp.uniformizerInteger (K := K) :
          DiffOp.CompletedPseudoDiffOpInteger (K := K)) : DiffOp.CompletedPseudoDiffOp K) = _
      rw [ih]
      show _ * ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ ((1 : ℕ) : ℤ) :
        (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) = _
      rw [← Units.val_mul, ← zpow_add]
      congr 2

/-- Conjugate of an integral scalar by a uniformizer power. -/
def DiffOp.uniformizerConj (k : ℕ) (a : DiffOp.CompletedPseudoDiffOpInteger (K := K)) :
    DiffOp.CompletedPseudoDiffOpInteger (K := K) :=
  ⟨((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ ((k : ℕ) : ℤ) :
      (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) *
    (a : DiffOp.CompletedPseudoDiffOp K) *
    ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (-((k : ℕ) : ℤ)) :
      (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K),
    DiffOp.uniformizer_conj_mem_integer (K := K) ((k : ℕ) : ℤ) a.2⟩

/-- The uniformizer power commutes past an integral scalar through its conjugate. -/
theorem DiffOp.uniformizerInteger_pow_mul (k : ℕ)
    (a : DiffOp.CompletedPseudoDiffOpInteger (K := K)) :
    DiffOp.uniformizerInteger (K := K) ^ k * a =
      DiffOp.uniformizerConj (K := K) k a * DiffOp.uniformizerInteger (K := K) ^ k := by
  apply Subtype.ext
  show ((DiffOp.uniformizerInteger (K := K) ^ k :
      DiffOp.CompletedPseudoDiffOpInteger (K := K)) : DiffOp.CompletedPseudoDiffOp K) *
      (a : DiffOp.CompletedPseudoDiffOp K) =
    (DiffOp.uniformizerConj (K := K) k a : DiffOp.CompletedPseudoDiffOp K) *
      ((DiffOp.uniformizerInteger (K := K) ^ k :
        DiffOp.CompletedPseudoDiffOpInteger (K := K)) : DiffOp.CompletedPseudoDiffOp K)
  rw [DiffOp.coe_uniformizerInteger_pow]
  show _ = (((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ ((k : ℕ) : ℤ) :
      (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) *
    (a : DiffOp.CompletedPseudoDiffOp K) *
    ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (-((k : ℕ) : ℤ)) :
      (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K)) * _
  rw [mul_assoc, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero, Units.val_one, mul_one]

variable {Q : Type*} [AddCommGroup Q] [Module (DiffOp.CompletedPseudoDiffOpInteger (K := K)) Q]

set_option synthInstance.maxHeartbeats 400000 in
/-- Vectors annihilated by a fixed uniformizer power form a submodule. -/
def DiffOp.uniformizerTorsion (k : ℕ) :
    Submodule (DiffOp.CompletedPseudoDiffOpInteger (K := K)) Q where
  carrier := {w | (DiffOp.uniformizerInteger (K := K)) ^ k • w = 0}
  add_mem' := by
    intro v w hv hw
    show _ • (v + w) = 0
    rw [smul_add, hv, hw, add_zero]
  zero_mem' := by
    show _ • (0 : Q) = 0
    rw [smul_zero]
  smul_mem' := by
    intro a v hv
    show (DiffOp.uniformizerInteger (K := K)) ^ k • (a • v) = 0
    rw [smul_smul, DiffOp.uniformizerInteger_pow_mul, ← smul_smul]
    show _ • ((DiffOp.uniformizerInteger (K := K)) ^ k • v) = 0
    rw [hv, smul_zero]

@[simp] theorem DiffOp.mem_uniformizerTorsion (k : ℕ) (w : Q) :
    w ∈ DiffOp.uniformizerTorsion (K := K) (Q := Q) k ↔
      (DiffOp.uniformizerInteger (K := K)) ^ k • w = 0 := Iff.rfl


set_option synthInstance.maxHeartbeats 400000 in
/-- A finitely generated module killed by the uniformizer has finite length. -/
theorem DiffOp.length_ne_top_of_fg_of_uniformizer_smul_eq_zero
    (hfin : (⊤ : Submodule (DiffOp.CompletedPseudoDiffOpInteger (K := K)) Q).FG)
    (h : ∀ v : Q, DiffOp.uniformizerInteger (K := K) • v = 0) :
    Module.length (DiffOp.CompletedPseudoDiffOpInteger (K := K)) Q ≠ ⊤ := by
  classical
  obtain ⟨s, hs⟩ := hfin
  have hbound := DiffOp.length_span_le_card_of_uniformizer_smul_eq_zero (K := K) s
    (fun q _ => h q)
  rw [hs] at hbound
  have hequiv : Module.length (DiffOp.CompletedPseudoDiffOpInteger (K := K))
      ↥(⊤ : Submodule (DiffOp.CompletedPseudoDiffOpInteger (K := K)) Q) =
      Module.length (DiffOp.CompletedPseudoDiffOpInteger (K := K)) Q := by
    refine le_antisymm ?_ ?_
    · exact Module.length_le_of_injective (Submodule.topEquiv).toLinearMap
        (Submodule.topEquiv).injective
    · exact Module.length_le_of_injective (Submodule.topEquiv (R := _) (M := Q)).symm.toLinearMap
        (Submodule.topEquiv (R := _) (M := Q)).symm.injective
  rw [hequiv] at hbound
  intro htop
  rw [htop] at hbound
  exact absurd hbound (by simp)

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **A finitely generated module killed by a uniformizer power has finite length.** -/
theorem DiffOp.length_ne_top_of_fg_of_uniformizer_pow_smul_eq_zero :
    ∀ (k : ℕ) {Q : Type*} [AddCommGroup Q]
      [Module (DiffOp.CompletedPseudoDiffOpInteger (K := K)) Q]
      (A : Submodule (DiffOp.CompletedPseudoDiffOpInteger (K := K)) Q), A.FG →
      (∀ v ∈ A, (DiffOp.uniformizerInteger (K := K)) ^ k • v = 0) →
      Module.length (DiffOp.CompletedPseudoDiffOpInteger (K := K)) ↥A ≠ ⊤ := by
  intro k
  induction k with
  | zero =>
      intro Q _ _ A _ hk
      have hbot : A = ⊥ := by
        refine le_antisymm (fun v hv => ?_) bot_le
        have hv0 := hk v hv
        rw [pow_zero, one_smul] at hv0
        exact Submodule.mem_bot _ |>.2 hv0
      rw [hbot]
      have hsubs : Subsingleton
          ↥(⊥ : Submodule (DiffOp.CompletedPseudoDiffOpInteger (K := K)) Q) := inferInstance
      rw [Module.length_eq_zero_iff.2 hsubs]
      simp
  | succ k ih =>
      intro Q _ _ A hA hk
      classical
      obtain ⟨s, hs⟩ := hA
      have hsA : ∀ x ∈ s, x ∈ A := by
        intro x hx
        rw [← hs]
        exact Submodule.subset_span hx
      set B := Submodule.span (DiffOp.CompletedPseudoDiffOpInteger (K := K))
        ((s.image (fun v => DiffOp.uniformizerInteger (K := K) • v) :
          Finset Q) : Set Q) with hB
      have hBA : B ≤ A := by
        rw [hB, Submodule.span_le]
        intro w hw
        rw [Finset.coe_image, Set.mem_image] at hw
        obtain ⟨x, hx, rfl⟩ := hw
        exact A.smul_mem _ (hsA x hx)
      have hBfg : B.FG := ⟨s.image (fun v => DiffOp.uniformizerInteger (K := K) • v), rfl⟩
      have hBk : ∀ w ∈ B, (DiffOp.uniformizerInteger (K := K)) ^ k • w = 0 := by
        have hle : B ≤ DiffOp.uniformizerTorsion (K := K) (Q := Q) k := by
          rw [hB, Submodule.span_le]
          intro w hw
          rw [Finset.coe_image, Set.mem_image] at hw
          obtain ⟨x, hx, rfl⟩ := hw
          show (DiffOp.uniformizerInteger (K := K)) ^ k •
            (DiffOp.uniformizerInteger (K := K) • x) = 0
          rw [smul_smul, ← pow_succ]
          exact hk x (hsA x hx)
        exact fun w hw => hle hw
      have hAB : ∀ v ∈ A, DiffOp.uniformizerInteger (K := K) • v ∈ B := by
        intro v hv
        rw [← hs] at hv
        induction hv using Submodule.span_induction with
        | mem x hx =>
            refine Submodule.subset_span ?_
            rw [Finset.coe_image]
            exact Set.mem_image_of_mem _ hx
        | zero => rw [smul_zero]; exact B.zero_mem
        | add x y _ _ ihx ihy => rw [smul_add]; exact B.add_mem ihx ihy
        | smul a x _ ihx =>
            rw [smul_smul, ← pow_one (DiffOp.uniformizerInteger (K := K)),
              DiffOp.uniformizerInteger_pow_mul, pow_one, ← smul_smul]
            exact B.smul_mem _ ihx
      set P : Submodule (DiffOp.CompletedPseudoDiffOpInteger (K := K)) ↥A :=
        B.comap A.subtype with hP
      have hsplit := Module.length_eq_add_of_exact P.subtype P.mkQ
        Subtype.val_injective (Submodule.mkQ_surjective P) (LinearMap.exact_subtype_mkQ P)
      have hPlen : Module.length (DiffOp.CompletedPseudoDiffOpInteger (K := K)) ↥P =
          Module.length (DiffOp.CompletedPseudoDiffOpInteger (K := K)) ↥B := by
        refine le_antisymm ?_ ?_
        · exact Module.length_le_of_injective
            (Submodule.comapSubtypeEquivOfLe hBA).toLinearMap
            (Submodule.comapSubtypeEquivOfLe hBA).injective
        · exact Module.length_le_of_injective
            (Submodule.comapSubtypeEquivOfLe hBA).symm.toLinearMap
            (Submodule.comapSubtypeEquivOfLe hBA).symm.injective
      have hPne : Module.length (DiffOp.CompletedPseudoDiffOpInteger (K := K)) ↥P ≠ ⊤ := by
        rw [hPlen]
        exact ih B hBfg hBk
      have hQfg : (⊤ : Submodule (DiffOp.CompletedPseudoDiffOpInteger (K := K))
          (↥A ⧸ P)).FG := by
        have hAfin : (⊤ : Submodule (DiffOp.CompletedPseudoDiffOpInteger (K := K)) ↥A).FG := by
          rw [← Module.Finite.iff_fg]
          rw [Module.Finite.iff_fg]
          exact (Submodule.fg_top A).2 ⟨s, hs⟩
        obtain ⟨u, hu⟩ := hAfin
        refine ⟨u.image P.mkQ, ?_⟩
        rw [Finset.coe_image, ← Submodule.map_span, hu, Submodule.map_top,
          LinearMap.range_eq_top.2 (Submodule.mkQ_surjective P)]
      have hQne : Module.length (DiffOp.CompletedPseudoDiffOpInteger (K := K)) (↥A ⧸ P) ≠ ⊤ := by
        refine DiffOp.length_ne_top_of_fg_of_uniformizer_smul_eq_zero hQfg ?_
        intro y
        induction y using Quotient.inductionOn with
        | _ z =>
            show P.mkQ (DiffOp.uniformizerInteger (K := K) • z) = 0
            rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
            exact hAB (z : Q) z.2
      rw [hsplit]
      exact WithTop.add_ne_top.2 ⟨hPne, hQne⟩

end

end GaloisForLFunctions.HTGeometry
