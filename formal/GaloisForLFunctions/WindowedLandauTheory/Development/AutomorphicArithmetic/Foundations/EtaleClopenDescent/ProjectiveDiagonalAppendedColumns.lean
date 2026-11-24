import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveDiagonalAppendScaling
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.NormalizedBaseColumn
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.KoszulAppendedWeights
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.DiagonalContractionScalars
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveDiagonalLocalClass

/-! Function-field diagonal equations can be added without changing
the identity action on the base-coordinate components. -/

noncomputable section

open GlobalTheory.CechDR GlobalTheory.SchemeCohomology GlobalTheory.WH
open GlobalTheory.WH.WeightedChartSystem
open scoped GlobalTheory.CechDR GlobalTheory.SchemeCohomology TensorProduct

namespace GlobalTheory.PD

variable {k F E κ : Type} [Field k] [CharZero k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  [LinearOrder κ] [Fintype κ] {d : ℕ} {x : Fin (d + 1) → F} {q p : ℕ}
  {n : κ → ℕ × ℕ} {z : κ → E ⊗[k] E}

local instance {r : ℕ} : IsScalarTower k F (ExteriorDifferentials k E r) :=
  IsScalarTower.to₁₂₄ k F E (ExteriorDifferentials k E r)

local notation "V" => ExteriorDifferentials k E q ⊗[k] ExteriorDifferentials k E p
local notation "n₀" => (fun _ : DiagonalIndex d => ((1, 1) : ℕ × ℕ))

private theorem map_constColumn_mem_cycles_of_commute {k ι M : Type}
    [Field k] [LinearOrder ι] [AddCommGroup M] [Module k M]
    (P : Submodule k M) (w : ι → Module.End k M) (u : Module.End k M)
    (hu : P ≤ P.comap u) (hw : ∀ l, Commute (w l) u)
    {m : ℤ} {b : Finset ι → M} (hb : b ∈ (acx (fun _ => P) w).Z m) :
    (fun L => u (b L)) ∈ (acx (fun _ => P) w).Z m := by
  refine ⟨acx_mem_terms_iff.mpr (fun L => ?_), ?_⟩
  · have hL := acx_mem_terms_iff.mp hb.1 L
    change u (b L) ∈ if (L.card : ℤ) = m then P else ⊥
    split_ifs at hL ⊢
    · exact hu hL
    · rw [(Submodule.mem_bot k).mp hL, map_zero]
      exact zero_mem _
  · have hD : wd w b = 0 := hb.2
    change wd w (fun L => u (b L)) = 0
    funext L
    calc
      wd w (fun L => u (b L)) L = u (wd w b L) := by
        rw [wd_apply, wd_apply, map_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [map_zsmul]
        exact congrArg (fun v : M => cubeSign L l • v) (LinearMap.congr_fun (hw l) (b (L.erase l)))
      _ = 0 := by simp only [hD, Pi.zero_apply, map_zero]

private theorem scaled_appended_column {k ι κ M : Type} [Field k]
    [LinearOrder ι] [LinearOrder κ] [Fintype ι] [Fintype κ] [AddCommGroup M] [Module k M]
    (P : Submodule k M) (w : ι ⊕ₗ κ → Module.End k M)
    (A : Cx k (Finset (ι ⊕ₗ κ) → M)) (B : Cx k (Finset κ → M))
    (e : (Finset (ι ⊕ₗ κ) → M) ≃ₗ[k] (Finset (ι ⊕ₗ κ) → M))
    (e₀ : (Finset κ → M) ≃ₗ[k] (Finset κ → M))
    (C : Cx k (Finset (ι ⊕ₗ κ) → M)) (D : Cx k (Finset κ → M))
    (hC : C = acx (fun _ => P) w)
    (hD : D = acx (fun _ => P) (fun j : κ => w (toLex (Sum.inr j))))
    (hcomm : ∀ i j, Commute (w i) (w j)) (hP : ∀ i, P ≤ P.comap (w i)) (d : ℤ)
    (hE : ∀ m < d, D.Z m ≤ D.B m)
    (hZ : ∀ m a, e a ∈ A.Z m ↔ a ∈ C.Z m)
    (hB : ∀ m a, e a ∈ A.B m ↔ a ∈ C.B m)
    (hZ₀ : ∀ m a, e₀ a ∈ B.Z m ↔ a ∈ D.Z m)
    (hB₀ : ∀ m a, e₀ a ∈ B.B m ↔ a ∈ D.B m)
    (hr : ∀ a L, e a (uni (∅ : Finset ι) L) = e₀ (fun J => a (uni ∅ J)) L)
    (L : Finset κ) (R : M → Prop) (H : (Finset κ → M) → Prop)
    (htop : ∀ v ∈ B.Z d, R (v L) → v ∈ B.B d)
    (hnew : ∀ v, H v → ∀ i : ι,
      (fun J => w (toLex (Sum.inl i)) (e₀.symm v J)) ∈
        D.Z d →
      (fun J => w (toLex (Sum.inl i)) (e₀.symm v J)) ∈
        D.B d) :
    (∀ m < d, A.Z m ≤ A.B m) ∧
    (∀ c ∈ A.Z d, R (c (uni (∅ : Finset ι) L)) → c ∈ A.B d) ∧
    (∀ v ∈ B.Z d, H v → ∃ c ∈ A.Z d, ∀ J, c (uni (∅ : Finset ι) J) = v J) := by
  subst C
  subst D
  refine ⟨?_, ?_, ?_⟩
  · intro m hm c hc
    let a := e.symm c
    have he : e a = c := e.apply_symm_apply c
    have ha := (hZ m a).mp (he.symm ▸ hc)
    have hb := appended_mem_boundary hcomm hP hE ha (le_of_lt hm) (fun hm' => (hm.ne hm').elim)
    exact he ▸ (hB m a).mpr hb
  · intro c hc hzero
    let a := e.symm c
    let b (J : Finset κ) := a (uni ∅ J)
    have he : e a = c := e.apply_symm_apply c
    have ha := (hZ d a).mp (he.symm ▸ hc)
    have hb := appended_restrict_mem_cycles ha
    have hc₀ : e₀ b ∈ B.Z d := (hZ₀ d b).mpr hb
    have hR : R (e₀ b L) := by
      rw [← hr a L, he]
      exact hzero
    have hb₀ := (hB₀ d b).mp (htop (e₀ b) hc₀ hR)
    exact he ▸ (hB d a).mpr (appended_mem_boundary hcomm hP hE ha (le_refl _) (fun _ => hb₀))
  · intro v hv hid
    let b := e₀.symm v
    have he : e₀ b = v := e₀.apply_symm_apply v
    have hb := (hZ₀ d b).mp (he.symm ▸ hv)
    have hLift (i : ι) : (fun J => w (toLex (Sum.inl i)) (b J)) ∈
        (acx (fun _ => P) (fun j : κ => w (toLex (Sum.inr j)))).B d :=
      hnew v hid i (map_constColumn_mem_cycles_of_commute P (fun j => w (toLex (Sum.inr j)))
        (w (toLex (Sum.inl i))) (hP _) (fun j => hcomm (toLex (Sum.inr j)) _) hb)
    obtain ⟨a, ha, hac⟩ := exists_cocycle_appending_weights hcomm hP hE hb hLift
    refine ⟨e a, (hZ d a).mpr ha, fun J => ?_⟩
    rw [hr, funext hac, he]

omit [CharZero k] in
private theorem tensorContraction_appendedAction_eq_zero (τ : DR k E →ₗ[E] E)
    (hτ : Function.Surjective ((traceWedgeLeftDual (F := F) (p := p) (q := q) τ).flip))
    {v : V} {c : F}
    (hv : ∀ a : ExteriorDifferentials k E p,
      tensorContraction ((traceWedgeLeftDual (F := F) τ).flip a) v = c • a)
    (u : F ⊗[k] F) (s : E ⊗[k] E) (hs : Algebra.TensorProduct.lmul' k s = 0)
    (f : ExteriorDifferentials k E q →ₗ[F] F) :
    tensorContraction f (tensorScalarAction s (tensorScalarAction u v)) = 0 := by
  obtain ⟨a, rfl⟩ := hτ f
  have h (b : ExteriorDifferentials k E p) :
      tensorContraction ((traceWedgeLeftDual (F := F) τ).flip b) (tensorScalarAction u v) =
        ((Algebra.TensorProduct.lmul' k u) * c) • b := by
    rw [tensorContraction_action, hv, mul_smul]
  rw [traceWedgeContraction_act_eq (F := F) (p := p) (q := q) τ h, hs, zero_smul]

private theorem normalizedBaseColumn_action_mem_boundary (H : IsFinCover k E x)
    (τ : DR k E →ₗ[E] E)
    (hτ : Function.Surjective ((traceWedgeLeftDual (F := F) (p := p) (q := q) τ).flip))
    {I J : Finset (Fin (d + 1))} {i j : Fin (d + 1)} (hi : i ∈ I) (hj : j ∈ J)
    (v : Finset (DiagonalIndex d) → V)
    (hv : ∀ L, ∃ c : F, ∀ a : ExteriorDifferentials k E p,
      tensorContraction ((traceWedgeLeftDual (F := F) τ).flip a) (v L) = c • a)
    (s : E ⊗[k] E) (hs : Algebra.TensorProduct.lmul' k s = 0) :
    let T := diagonalChartSystem (E := E) H.pd q p
    let b := (T.scaleColumn n₀ i j).symm v
    let a := fun L => tensorScalarAction s (b L)
    let C := normalizedBaseColumn (E := E) H.pd q p I J i j
    a ∈ C.Z (d : ℤ) → a ∈ C.B (d : ℤ) := by
  intro T b a C ha
  apply (H.normalizedBaseColumn_exact_and_boundary q p hi hj).2 a ha
  intro f
  let L := selectedIndices (diagonalIndexEmbedding j)
  obtain ⟨c, hc⟩ := hv L
  let u : F ⊗[k] F := ((T.normalizationProduct n₀ i j L)⁻¹ : (F ⊗[k] F)ˣ)
  change tensorContraction f (tensorScalarAction s (tensorScalarAction u (v L))) = 0
  exact tensorContraction_appendedAction_eq_zero (F := F) (p := p) (q := q) τ hτ hc u s hs f

/-- The enlarged column remains exact below the dimension. A top
cycle is a boundary when its restricted selected value contracts to zero.
A base column acting by diagonal scalars extends to the enlarged column. -/
theorem IsFinCover.appendedDiagonalColumn (H : IsFinCover k E x)
    (τ : DR k E →ₗ[E] E) (hτ : IsTop (x := x) τ) (hpq : p + q = d)
    (hz : NormalizedDiagonalEquations H.pd n z)
    {I J : Finset (Fin (d + 1))} {i j : Fin (d + 1)} (hi : i ∈ I) (hj : j ∈ J) :
    let T := diagonalChartSystem (E := E) H.pd q p
    let W := normalizedDiagonalSystem (E := E) H.pd q p
    let B := T.columnComplex n₀ T.homogeneousMinor I J
    let A := W.columnComplex (appendedDiagonalDegrees n) (appendedDiagonalWeights H.pd q p z) I J
    let L := selectedIndices (diagonalIndexEmbedding j)
    (∀ m < (d : ℤ), A.Z m ≤ A.B m) ∧
    (∀ c ∈ A.Z (d : ℤ),
      (∀ f : ExteriorDifferentials k E q →ₗ[F] F, tensorContraction f (c (uni ∅ L)) = 0) →
      c ∈ A.B (d : ℤ)) ∧
    (∀ v ∈ B.Z (d : ℤ), (∀ L, ∃ r : F, ∀ a : ExteriorDifferentials k E p,
        tensorContraction ((traceWedgeLeftDual (F := F) τ).flip a) (v L) = r • a) →
      ∃ c ∈ A.Z (d : ℤ), ∀ L, c (uni ∅ L) = v L) := by
  let T := diagonalChartSystem (E := E) H.pd q p
  let W := normalizedDiagonalSystem (E := E) H.pd q p
  let gT := diagonalChartSystem_good (E := E) H.pd q p
  let gW := normalizedDiagonalSystem_good (E := E) H.pd q p
  let aN : κ ⊕ₗ DiagonalIndex d → ℕ × ℕ := appendedDiagonalDegrees n
  let aZ := appendedDiagonalWeights H.pd q p z
  let r : κ ⊕ₗ DiagonalIndex d → E ⊗[k] E := W.normalizedWeight aN aZ i j
  let P : Submodule k V := T.M I J
  let w (l : κ ⊕ₗ DiagonalIndex d) : Module.End k V := W.act (r l)
  let A := W.columnComplex aN aZ I J
  let B := T.columnComplex n₀ T.homogeneousMinor I J
  let C := acx (k := k) (ι := κ ⊕ₗ DiagonalIndex d) (M := V) (fun _ => P) w
  let D := acx (k := k) (ι := DiagonalIndex d) (M := V) (fun _ => P) fun l => w (toLex (Sum.inr l))
  let B₀ := normalizedBaseColumn (E := E) H.pd q p I J i j
  let e := W.scaleColumn aN i j
  let e₀ := T.scaleColumn n₀ i j
  have hD : D = B₀ := by
    have hw : (fun l : DiagonalIndex d => w (toLex (Sum.inr l))) =
        fun l => T.act (T.normalizedWeight n₀ T.homogeneousMinor i j l) :=
      funext (appendedDiagonal_baseAction H.pd q p n z i j)
    exact congrArg (acx (k := k) (ι := DiagonalIndex d) (M := V) (fun _ => P)) hw
  have hex (m : ℤ) (hm : m < (d : ℤ)) : D.Z m ≤ D.B m :=
    hD.symm ▸ (H.normalizedBaseColumn_exact_and_boundary q p hi hj).1 m hm
  have hcomm (a b : κ ⊕ₗ DiagonalIndex d) : Commute (w a) (w b) := (Commute.all _ _).map W.act
  have hP (l : κ ⊕ₗ DiagonalIndex d) : P ≤ P.comap (w l) := by
    intro v hv
    exact gW.stab I J ⟨i, hi⟩ ⟨j, hj⟩ (r l)
      (W.normalizedWeight_mem gW (appendedDiagonal_admitted H.pd q p hz) hi hj l) v hv
  have hZ (m : ℤ) (a : Finset (κ ⊕ₗ DiagonalIndex d) → V) : e a ∈ A.Z m ↔ a ∈ C.Z m :=
    W.scaleColumn_mem_cycles_iff gW aN aZ hi hj m a
  have hB (m : ℤ) (a : Finset (κ ⊕ₗ DiagonalIndex d) → V) : e a ∈ A.B m ↔ a ∈ C.B m :=
    W.scaleColumn_mem_boundaries_iff gW aN aZ hi hj m a
  have hZ₀ (m : ℤ) (a : Finset (DiagonalIndex d) → V) : e₀ a ∈ B.Z m ↔ a ∈ D.Z m :=
    hD.symm ▸ T.scaleColumn_mem_cycles_iff gT n₀ T.homogeneousMinor hi hj m a
  have hB₀ (m : ℤ) (a : Finset (DiagonalIndex d) → V) : e₀ a ∈ B.B m ↔ a ∈ D.B m :=
    hD.symm ▸ T.scaleColumn_mem_boundaries_iff gT n₀ T.homogeneousMinor hi hj m a
  have hr (a : Finset (κ ⊕ₗ DiagonalIndex d) → V) (L : Finset (DiagonalIndex d)) :
      e a (uni ∅ L) = e₀ (fun L => a (uni ∅ L)) L :=
    appendedDiagonal_scale_restrict H.pd q p n i j a L
  have hsurj : Function.Surjective ((traceWedgeLeftDual (F := F) (p := p) (q := q) τ).flip) := by
    change Function.Surjective (traceWedgeDual (F := F) (p := q) (q := p) τ)
    exact (H.traceWedgeDual_bijective τ hτ (by simpa only [Nat.add_comm q p] using hpq : q + p = d)).2
  let R (v : V) : Prop := ∀ f : ExteriorDifferentials k E q →ₗ[F] F, tensorContraction f v = 0
  let Hact (v : Finset (DiagonalIndex d) → V) : Prop := ∀ L,
    ∃ r : F, ∀ a : ExteriorDifferentials k E p,
      tensorContraction ((traceWedgeLeftDual (F := F) τ).flip a) (v L) = r • a
  let L := selectedIndices (diagonalIndexEmbedding j)
  have htop : ∀ v ∈ B.Z (d : ℤ), R (v L) → v ∈ B.B (d : ℤ) :=
    (H.diagonalColumn_exact_and_boundary q p hi hj).2
  have hnew (v : Finset (DiagonalIndex d) → V) (hid : Hact v) (a : κ)
      (hc : (fun L => w (toLex (Sum.inl a)) (e₀.symm v L)) ∈ D.Z (d : ℤ)) :
      (fun L => w (toLex (Sum.inl a)) (e₀.symm v L)) ∈ D.B (d : ℤ) := by
    let s : E ⊗[k] E := r (toLex (Sum.inl a))
    let U : (E ⊗[k] E)ˣ := W.weightUnit aN i j (toLex (Sum.inl a))
    have hs : Algebra.TensorProduct.lmul' k s = 0 := by
      change Algebra.TensorProduct.lmul' k (z a * ((U⁻¹ : (E ⊗[k] E)ˣ) : E ⊗[k] E)) = 0
      rw [map_mul, hz.vanishes a, zero_mul]
    let t (L : Finset (DiagonalIndex d)) : V := tensorScalarAction s (e₀.symm v L)
    have ht : t ∈ B₀.Z (d : ℤ) := hD ▸ hc
    have htb : t ∈ B₀.B (d : ℤ) :=
      normalizedBaseColumn_action_mem_boundary (p := p) (q := q) H τ hsurj hi hj v hid s hs ht
    exact hD.symm ▸ htb
  have hresult := scaled_appended_column (k := k) (ι := κ) (κ := DiagonalIndex d) (M := V)
    P w A B e e₀ C D rfl rfl hcomm hP d hex hZ hB hZ₀ hB₀ hr L R Hact htop hnew
  exact hresult

end GlobalTheory.PD
