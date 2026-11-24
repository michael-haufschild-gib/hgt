import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveDiagonalAction
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.DiagonalCocycleResolution

/-! The graded diagonal cocycle embeds into the full de Rham
coefficient space and retains its identity action on regular cochains. -/

noncomputable section

open GlobalTheory.CechDR GlobalTheory.SchemeCohomology GlobalTheory.WH
open GlobalTheory.WH.WeightedChartSystem
open scoped GlobalTheory.CechDR GlobalTheory.SchemeCohomology TensorProduct

namespace GlobalTheory.PD

variable {k F E : Type} [Field k] [CharZero k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  {d : ℕ} {x : Fin (d + 1) → F} {p q : ℕ}

local instance {r : ℕ} : IsScalarTower k F (ExteriorDifferentials k E r) :=
  IsScalarTower.to₁₂₄ k F E (ExteriorDifferentials k E r)

private abbrev formInclusion (r : ℕ) :
    ExteriorDifferentials k E r →ₗ[k] DR k E :=
  (ExteriorDifferentials k E r).subtype.restrictScalars k

private abbrev formTensorInclusion (q p : ℕ) :
    ExteriorDifferentials k E q ⊗[k] ExteriorDifferentials k E p →ₗ[k] DR k E ⊗[k] DR k E :=
  TensorProduct.map (formInclusion q) (formInclusion p)

private abbrev chartForms (r : ℕ) (I : Finset (Fin (d + 1))) := omB k E (rB k E x I) r

/-- The weight-free Čech projection of a typed form-tensor cochain. -/
def diagonalCechPart {κ : Type} [LinearOrder κ]
    (c : Finset (ChartPair d ⊕ₗ κ) → ExteriorDifferentials k E q ⊗[k] ExteriorDifferentials k E p) :
    Finset (ChartPair d) → DR k E ⊗[k] DR k E :=
  mapCochain (ι := ChartPair d)
    (M := ExteriorDifferentials k E q ⊗[k] ExteriorDifferentials k E p)
    (N := DR k E ⊗[k] DR k E) (formTensorInclusion q p) (chartPart c)

private theorem residueTensor_include (τ : DR k E →ₗ[E] E) (ρ : F →ₗ[k] k)
    (t : ExteriorDifferentials k E q ⊗[k] ExteriorDifferentials k E p)
    (v : ExteriorDifferentials k E p) :
    formInclusion p (logarithmicResidueTensor ρ (traceWedgeTensorCoefficient (F := F) τ t v)) =
      traceWedgeTensorAction τ ρ (TensorProduct.map (formInclusion q) (formInclusion p) t)
        (formInclusion p v) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | tmul a b =>
    rw [traceWedgeTensorCoefficient_tmul, logarithmicResidueTensor_tmul, map_smul,
      TensorProduct.map_tmul, traceWedgeTensorAction_tmul, topResidue_apply, traceWedgeLeftDual_apply]
    rfl

private theorem mapCochain_chartPart_cycles {k S M N κ : Type} [Field k]
    [CommRing S] [Algebra k S] [LinearOrder κ] [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N] {d : ℕ}
    (T : WeightedChartSystem k d S M)
    (B : Finset (Fin (d + 1)) → Finset (Fin (d + 1)) → Submodule k N)
    (f : M →ₗ[k] N) (hAB : ∀ I J, T.M I J ≤ (B I J).comap f)
    (n : κ → ℕ × ℕ) (z : κ → S)
    {j : ℤ} {c : Finset (ChartPair d ⊕ₗ κ) → M} (hc : c ∈ (T.complex n z).Z j) :
    mapCochain f (chartPart c) ∈ (mixedCech B).Z j := by
  let a : Finset (ChartPair d) → M := chartPart c
  have ha : a ∈ (mixedCech T.M).Z j := T.chartPart_mem_cycles (n := n) (z := z) (p := j) hc
  change mapCochain f a ∈ (mixedCech B).Z j
  refine ⟨acx_mem_terms_iff.mpr (fun s => ?_), ?_⟩
  · have hm := acx_mem_terms_iff.mp ha.1 s
    change f (a s) ∈ if (s.card : ℤ) = j then
      (if (lft s).Nonempty ∧ (rgt s).Nonempty then B (lft s) (rgt s) else ⊥) else ⊥
    split_ifs at hm ⊢
    · exact hAB _ _ hm
    · rw [(Submodule.mem_bot k).mp hm, map_zero]
      exact zero_mem _
    · rw [(Submodule.mem_bot k).mp hm, map_zero]
      exact zero_mem _
  · have hd : wd (1 : ChartPair d → Module.End k M) a = 0 := ha.2
    change wd (1 : ChartPair d → Module.End k N) (mapCochain f a) = 0
    rw [wd_one] at hd ⊢
    rw [← mapCochain_delta, hd, map_zero]

omit [CharZero k] in
private theorem regularFormTensorInclusion_le (A B : Subalgebra k E) (q p : ℕ) :
    tensorChartLattice (regularExteriorLattice A q) (regularExteriorLattice B p) ≤
      (Submodule.map₂ (TensorProduct.mk k (DR k E) (DR k E))
        (omB k E A q) (omB k E B p)).comap (formTensorInclusion q p) := by
  refine Submodule.map₂_le.mpr ?_
  intro u hu v hv
  have hu' : (u : DR k E) ∈ omB k E A q := hu
  have hv' : (v : DR k E) ∈ omB k E B p := hv
  change TensorProduct.map (formInclusion q) (formInclusion p) (u ⊗ₜ[k] v) ∈
    Submodule.map₂ (TensorProduct.mk k (DR k E) (DR k E)) (omB k E A q) (omB k E B p)
  rw [TensorProduct.map_tmul]
  exact Submodule.apply_mem_map₂ _ hu' hv'

private theorem diagonalCechPart_mem_cycles (h : IsFinCover k E x)
    {c : Finset (ChartPair d ⊕ₗ DiagonalIndex d) →
      ExteriorDifferentials k E q ⊗[k] ExteriorDifferentials k E p}
    (hc : let T := diagonalChartSystem (E := E) h.pd q p
      c ∈ (T.complex (fun _ => (1, 1)) T.homogeneousMinor).Z ((d : ℤ) + 2)) :
    diagonalCechPart (k := k) (E := E) (p := p) (q := q) c ∈
      (mixedCech (fun I J => Submodule.map₂ (TensorProduct.mk k (DR k E) (DR k E))
        (chartForms (k := k) (E := E) (x := x) q I) (chartForms (k := k) (E := E) (x := x) p J))).Z
        ((d : ℤ) + 2) := by
  let T := diagonalChartSystem (E := E) h.pd q p
  let f : ExteriorDifferentials k E q ⊗[k] ExteriorDifferentials k E p →ₗ[k] DR k E ⊗[k] DR k E :=
    formTensorInclusion q p
  let B (I J : Finset (Fin (d + 1))) :=
    Submodule.map₂ (TensorProduct.mk k (DR k E) (DR k E))
      (chartForms (k := k) (E := E) (x := x) q I) (chartForms (k := k) (E := E) (x := x) p J)
  let n : DiagonalIndex d → ℕ × ℕ := fun _ => (1, 1)
  have hAB (I J : Finset (Fin (d + 1))) : T.M I J ≤ (B I J).comap f :=
    regularFormTensorInclusion_le (rB k E x I) (rB k E x J) q p
  exact mapCochain_chartPart_cycles (S := F ⊗[k] F)
    (M := ExteriorDifferentials k E q ⊗[k] ExteriorDifferentials k E p)
    (N := DR k E ⊗[k] DR k E) T B f hAB n T.homogeneousMinor (j := (d : ℤ) + 2) (c := c) hc

private theorem exists_lift_cech_cocycle {k ι M N : Type} [Field k] [LinearOrder ι]
    [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    (A : Finset ι → Submodule k M) (B : Finset ι → Submodule k N)
    (f : M →ₗ[k] N) (hf : Function.Injective f)
    (hAB : ∀ I, ∀ b ∈ B I, ∃ a ∈ A I, f a = b)
    {n : ℤ} {v : Finset ι → N} (hv : v ∈ (cech B).Z n) :
    ∃ a ∈ (cech A).Z n, mapCochain f a = v := by
  have hex (I : Finset ι) : ∃ a : M,
      a ∈ (if I.Nonempty ∧ (I.card : ℤ) = n + 1 then A I else ⊥) ∧ f a = v I := by
    have hI := Submodule.mem_pi.mp hv.1 I (Set.mem_univ I)
    split_ifs at hI ⊢
    · exact hAB I (v I) hI
    · exact ⟨0, zero_mem _, (f.map_zero).trans ((Submodule.mem_bot k).mp hI).symm⟩
  choose a ha hfa using hex
  have hav : mapCochain f a = v := funext hfa
  refine ⟨a, ⟨Submodule.mem_pi.mpr (fun I _ => ha I), ?_⟩, hav⟩
  have hd : deltaL k ι N v = 0 := hv.2
  have hz : mapCochain f (deltaL k ι M a) = 0 := by
    rw [mapCochain_delta, hav, hd]
  change deltaL k ι M a = 0
  funext I
  apply hf
  simpa only [mapCochain_apply, Pi.zero_apply, map_zero] using congrFun hz I

omit [CharZero k] in
private theorem exists_lift_regular_cocycle (m : ℕ) {v : Finset (Fin (d + 1)) → DR k E}
    (hv : v ∈ (cech (chartForms (k := k) (E := E) (x := x) p)).Z (m : ℤ)) :
    ∃ a ∈ (cech (fun I => regularExteriorLattice (rB k E x I) p)).Z (m : ℤ),
      mapCochain (formInclusion p) a = v := by
  let A (I : Finset (Fin (d + 1))) := regularExteriorLattice (rB k E x I) p
  let B (I : Finset (Fin (d + 1))) := chartForms (k := k) (E := E) (x := x) p I
  let e : ExteriorDifferentials k E p →ₗ[k] DR k E := formInclusion p
  have hAB (I : Finset (Fin (d + 1))) (b : DR k E) (hb : b ∈ B I) :
      ∃ a ∈ A I, e a = b := by
    have hp : b ∈ ExteriorDifferentials k E p := omB_le_degree (B := rB k E x I) (p := p) hb
    exact ⟨⟨b, hp⟩, hb, rfl⟩
  exact exists_lift_cech_cocycle (M := ExteriorDifferentials k E p) (N := DR k E)
    A B e Subtype.val_injective hAB hv

private theorem mapCochain_residueCup (τ : DR k E →ₗ[E] E) (ρ : F →ₗ[k] k)
    (c : Finset (ChartPair d ⊕ₗ DiagonalIndex d) →
      ExteriorDifferentials k E q ⊗[k] ExteriorDifferentials k E p)
    (a : Finset (Fin (d + 1)) → ExteriorDifferentials k E p) :
    let e : ExteriorDifferentials k E p →ₗ[k] DR k E := formInclusion p
    let μ := traceWedgeTensorCoefficient (F := F) (p := p) (q := q) τ
    mapCochain e (fun J => logarithmicResidueTensor ρ (cupAlongLeft μ a (chartPart c) J)) =
      cupAlongLeft (traceWedgeTensorAction τ ρ) (mapCochain e a) (diagonalCechPart c) := by
  intro e μ
  funext J
  simp only [mapCochain_apply, cupAlongLeft, cechCup_apply, map_sum, diagonalCechPart]
  exact Finset.sum_congr rfl fun i _ =>
    residueTensor_include τ ρ (chartPart c (uni (Finset.univ.filter (· ≤ i)) J))
      (a (Finset.univ.filter (i ≤ ·)))

/-- The Čech projection of a diagonal cocycle represents the identity
through the traced residue pairing in each cohomology degree. -/
theorem IsFinCover.diagonalCechPart_acts (h : IsFinCover k E x)
    (τ : DR k E →ₗ[E] E) (hτ : IsTop (x := x) τ) (ρ : F →ₗ[k] k) (hρ : IsRes x ρ)
    (hpq : p + q = d)
    {c : Finset (ChartPair d ⊕ₗ DiagonalIndex d) →
      ExteriorDifferentials k E q ⊗[k] ExteriorDifferentials k E p}
    (hc : let T := diagonalChartSystem (E := E) h.pd q p
      c ∈ (T.complex (fun _ => (1, 1)) T.homogeneousMinor).Z ((d : ℤ) + 2))
    (hL : Lev rightIndices (· ≤ (d : ℤ)) c)
    (hs : let T := diagonalChartSystem (E := E) h.pd q p
      ∀ (i j : Fin (d + 1)) (L : Finset (DiagonalIndex d)), L.card = d →
        ∀ b : ExteriorDifferentials k E p,
          tensorContraction ((traceWedgeLeftDual (F := F) τ).flip b) (c (uni (uni {i} {j}) L)) =
            (-1 : ℤ) ^ d • ((Algebra.TensorProduct.lmul' k
              (orderedMinor T.minorRows (uni {(0 : Fin (d + 1))} L))) • b)) :
    let z := diagonalCechPart (k := k) (E := E) (p := p) (q := q) c
    z ∈ (mixedCech (fun I J => Submodule.map₂ (TensorProduct.mk k (DR k E) (DR k E))
        (chartForms (k := k) (E := E) (x := x) q I) (chartForms (k := k) (E := E) (x := x) p J))).Z ((d : ℤ) + 2) ∧
      ∀ m : ℕ, ∀ v ∈ (cech (chartForms (k := k) (E := E) (x := x) p)).Z (m : ℤ),
        v - cupAlongLeft (traceWedgeTensorAction τ ρ) v z ∈ (cech (chartForms (k := k) (E := E) (x := x) p)).B (m : ℤ) := by
  intro z
  refine ⟨diagonalCechPart_mem_cycles (p := p) (q := q) h hc, ?_⟩
  intro m v hv
  let P (I : Finset (Fin (d + 1))) := chartForms (k := k) (E := E) (x := x) p I
  let A (I : Finset (Fin (d + 1))) := regularExteriorLattice (rB k E x I) p
  let e : ExteriorDifferentials k E p →ₗ[k] DR k E := formInclusion p
  obtain ⟨a, ha, hav⟩ := exists_lift_regular_cocycle (k := k) (E := E) (x := x) (p := p) m hv
  have hact := h.diagonal_action_eq_identity (p := p) (q := q) (m := m)
    τ hτ ρ hρ hpq hc hL hs ha
  have hm : IsMap (cech A) (cech P) (mapCochain e) :=
    isMap_mapCochain A P e (fun _ _ _ h' => h')
  obtain ⟨y, hy, hed⟩ := hact
  refine ⟨mapCochain e y, (hm ((m : ℤ) - 1) y hy).1, ?_⟩
  change (cech P).D (mapCochain e y) = v - cupAlongLeft (traceWedgeTensorAction τ ρ) v z
  rw [← (hm ((m : ℤ) - 1) y hy).2, hed, map_sub, mapCochain_residueCup, hav]

end GlobalTheory.PD
