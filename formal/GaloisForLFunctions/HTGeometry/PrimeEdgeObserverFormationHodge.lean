import GaloisForLFunctions.HTGeometry.SourceFormationHarmonicMechanics
import GaloisForLFunctions.HTGeometry.CommonCharacterFusionConservation
import GaloisForLFunctions.HTGeometry.DerivedSelectionGeometry.DerivedFibre

/-!
# Prime-edge observer formation, Hodge reconstruction, and bilateral properness

This file identifies the scalar observer complex of a finite literal prime-edge packet with the
zero-sum label complex.  Its centered representative is the Hodge harmonic component, signed
reversal acts isometrically, and the literal two-edge Hodge action is bilaterally summable exactly
at zero radial drift.
-/

open scoped BigOperators Differential UpperEndDifferentialInstances
  UpperEndComplexTowerInstances
open CategoryTheory
open _root_.HTGeometry
open _root_.RHTower

namespace GaloisForLFunctions.HTGeometry

noncomputable section

abbrev PrimeEdgePacket (r : ℕ) := Fin r → ℝ

/-- Consecutive edge `v_j-v_{j+1}` in the canonical finite vertex basis. -/
def primePathEdge (r : ℕ) (j : Fin r) : Fin (r + 1) → ℝ :=
  Pi.single j.castSucc 1 - Pi.single j.succ 1

/-- Prefix functional recovering one edge coefficient from a path boundary. -/
def primePathPrefix (r : ℕ) (i : Fin r) : (Fin (r + 1) → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ k ∈ Finset.Iic i.castSucc, x k
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum]

@[simp] theorem primePathPrefix_edge (r : ℕ) (i j : Fin r) :
    primePathPrefix r i (primePathEdge r j) = if j = i then 1 else 0 := by
  classical
  simp only [primePathPrefix, primePathEdge]
  by_cases hji : j = i
  · subst j
    simp
  · have hcases : j < i ∨ i < j := lt_or_gt_of_ne hji
    rcases hcases with hlt | hgt
    · have hsucc : j.succ ≤ i.castSucc := by
        exact Fin.mk_le_mk.mpr (by omega)
      simp [hji, hlt.le, hsucc]
    · have hcast : ¬j.castSucc ≤ i.castSucc := by
        exact not_le.mpr (Fin.mk_lt_mk.mpr hgt)
      have hsucc : ¬j.succ ≤ i.castSucc := by
        exact not_le.mpr (Fin.mk_lt_mk.mpr (by omega))
      simp [hji, hcast, hsucc]

/-- Consecutive path edges are linearly independent. -/
theorem primePathEdge_linearIndependent (r : ℕ) :
    LinearIndependent ℝ (primePathEdge r) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have h := congrArg (primePathPrefix r i) hc
  simpa using h

/-- Distinct prime-edge formation legs have trivial intersection. -/
theorem primePathEdge_span_inf_eq_bot {r : ℕ} {i j : Fin r} (hij : i ≠ j) :
    Submodule.span ℝ {primePathEdge r i} ⊓ Submodule.span ℝ {primePathEdge r j} = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rcases (Submodule.mem_span_singleton.mp hx.1) with ⟨a, rfl⟩
  rcases (Submodule.mem_span_singleton.mp hx.2) with ⟨b, hab⟩
  have hp := congrArg (primePathPrefix r i) hab
  have hji : j ≠ i := Ne.symm hij
  simp [hji] at hp
  have ha : a = 0 := hp.symm
  rw [ha]
  simp

/-- Finite path edges are the coefficient restrictions of the literal source edges. -/
theorem primePathEdge_eq_primeExponentEdge (r : ℕ) (j : Fin r) (e : Fin (r + 1)) :
    primePathEdge r j e = (primeExponentEdge j e : ℝ) := by
  classical
  by_cases h₀ : (e : ℕ) = (j : ℕ)
  · have he : e = j.castSucc := Fin.ext h₀
    subst e
    have hne : j.castSucc ≠ j.succ := by
      intro h
      have hv := congrArg Fin.val h
      simp at hv
    simp [primePathEdge, primeExponentEdge, hne]
  · by_cases h₁ : (e : ℕ) = (j : ℕ) + 1
    · have he : e = j.succ := Fin.ext h₁
      subst e
      have hne : j.castSucc ≠ j.succ := by
        intro h
        have hv := congrArg Fin.val h
        simp at hv
      simp [primePathEdge, primeExponentEdge, Ne.symm hne]
    · have hcast : e ≠ j.castSucc := by
        intro h
        apply h₀
        exact congrArg Fin.val h
      have hsucc : e ≠ j.succ := by
        intro h
        apply h₁
        exact congrArg Fin.val h
      simp [primePathEdge, primeExponentEdge, h₀, h₁, hcast, hsucc]

theorem primeExponentEdge_add_left (m a e : ℕ) :
    primeExponentEdge (m + a) (m + e) = primeExponentEdge a e := by
  simp only [primeExponentEdge]
  split_ifs <;> omega

/-- Translation identifies the finite path model with every literal source-edge block. -/
theorem primePathEdge_eq_shifted_primeExponentEdge (m r : ℕ)
    (j : Fin r) (e : Fin (r + 1)) :
    primePathEdge r j e = (primeExponentEdge (m + j) (m + e) : ℝ) := by
  rw [primeExponentEdge_add_left]
  exact primePathEdge_eq_primeExponentEdge r j e

/-- Literal real character response of edge `m + j`. -/
def primeEdgeResponse (q : ℝ) (m : ℕ) {r : ℕ} (j : Fin r) : ℝ :=
  q ^ (m + (j : ℕ)) * (1 - q)

theorem primeEdgeResponse_eq_characterEdge (q : ℝ) (m : ℕ) {r : ℕ} (j : Fin r) :
    (primeEdgeResponse q m j : ℂ) = complexCharacterEdge q (m + (j : ℕ)) := by
  simp [primeEdgeResponse, complexCharacterEdge, pow_succ]
  ring

theorem primeEdgeResponse_ne_zero {q : ℝ} (hq0 : q ≠ 0) (hq1 : q ≠ 1)
    (m : ℕ) {r : ℕ} (j : Fin r) :
    primeEdgeResponse q m j ≠ 0 := by
  exact mul_ne_zero (pow_ne_zero _ hq0) (sub_ne_zero.mpr (Ne.symm hq1))

/-- Observed image of one nonzero source leg. -/
def observedPrimeEdgeLeg (q : ℝ) (m : ℕ) {r : ℕ} (j : Fin r) : Submodule ℝ ℝ :=
  Submodule.span ℝ {primeEdgeResponse q m j}

theorem observedPrimeEdgeLeg_eq_top {q : ℝ} (hq0 : q ≠ 0) (hq1 : q ≠ 1)
    (m : ℕ) {r : ℕ} (j : Fin r) :
    observedPrimeEdgeLeg q m j = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rw [observedPrimeEdgeLeg, Submodule.mem_span_singleton]
  exact ⟨x / primeEdgeResponse q m j, by
    rw [smul_eq_mul, div_mul_cancel₀ x (primeEdgeResponse_ne_zero hq0 hq1 m j)]⟩

/-- Boundary of the observed two-term formation complex. -/
abbrev primeEdgeFormationBoundary (r : ℕ) : PrimeEdgePacket r →ₗ[ℝ] ℝ :=
  finiteLabelFusionLinearMap r

/-- Degree-zero formation charge: packet variations invisible to scalar fusion. -/
abbrev PrimeEdgeFormationCharge (r : ℕ) :=
  LinearMap.ker (primeEdgeFormationBoundary r)

/-- Short-complex realization `0 → ℝʳ →Σ ℝ` whose middle homology is the charge carrier. -/
def primeEdgeFormationKernelComplex (r : ℕ) : ShortComplex (ModuleCat ℝ) :=
  ShortComplex.mk
    (0 : ModuleCat.of ℝ (Fin 0 → ℝ) ⟶ ModuleCat.of ℝ (PrimeEdgePacket r))
    (ModuleCat.ofHom (primeEdgeFormationBoundary r)) (by simp)

/-- Literal formation homology is canonically the zero-sum packet subspace. -/
noncomputable def primeEdgeFormationHomologyIso (r : ℕ) :
    (primeEdgeFormationKernelComplex r).homology ≅
      ModuleCat.of ℝ (PrimeEdgeFormationCharge r) :=
  DerivedSelection.homologyIsoKer (primeEdgeFormationKernelComplex r) (by
    constructor
    intro x y
    funext i
    exact Fin.elim0 i)

/-- The second half of `0 → ℝʳ →Σ ℝ → 0`, whose homology is the coarse cokernel. -/
def primeEdgeFormationCoarseComplex (r : ℕ) : ShortComplex (ModuleCat ℝ) :=
  ShortComplex.mk (ModuleCat.ofHom (primeEdgeFormationBoundary r))
    (0 : ModuleCat.of ℝ ℝ ⟶ ModuleCat.of ℝ (Fin 0 → ℝ)) (by simp)

noncomputable def primeEdgeFormationCoarseHomologyIso (r : ℕ) :
    (primeEdgeFormationCoarseComplex r).homology ≅
      ModuleCat.of ℝ (ℝ ⧸ LinearMap.range (primeEdgeFormationBoundary r)) :=
  DerivedSelection.homologyIsoQuotRange (primeEdgeFormationCoarseComplex r) (by
    constructor
    intro x y
    funext i
    exact Fin.elim0 i)

theorem primeEdgeFormationBoundary_surjective {r : ℕ} (hr : 0 < r) :
    Function.Surjective (primeEdgeFormationBoundary r) :=
  finiteLabelFusionLinearMap_surjective hr

theorem primeEdgeFormationCoarseQuotient_subsingleton {r : ℕ} (hr : 0 < r) :
    Subsingleton (ℝ ⧸ LinearMap.range (primeEdgeFormationBoundary r)) := by
  have hrange : LinearMap.range (primeEdgeFormationBoundary r) = ⊤ :=
    LinearMap.range_eq_top.mpr (primeEdgeFormationBoundary_surjective hr)
  rw [hrange]
  refine ⟨fun a b => ?_⟩
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  rw [Submodule.Quotient.eq]
  trivial

/-- Surjectivity kills the coarse-target homology; only the zero-sum charge survives. -/
theorem primeEdgeFormationCoarseHomology_subsingleton {r : ℕ} (hr : 0 < r) :
    Subsingleton (primeEdgeFormationCoarseComplex r).homology := by
  let e := primeEdgeFormationCoarseHomologyIso r
  letI := primeEdgeFormationCoarseQuotient_subsingleton hr
  constructor
  intro x y
  have hxy : e.hom x = e.hom y := Subsingleton.elim _ _
  have := congrArg e.inv hxy
  simpa using this

theorem primeEdgeFormationCharge_finrank {r : ℕ} (hr : 0 < r) :
    Module.finrank ℝ (PrimeEdgeFormationCharge r) = r - 1 :=
  finiteLabelFusionLinearMap_finrank_ker hr

/-- Every nontrivial character observer produces the literal scalar-fusion formation law. -/
theorem primeEdge_literal_formation_charge {q : ℝ} (hq0 : q ≠ 0) (hq1 : q ≠ 1)
    (m : ℕ) {r : ℕ} (hr : 0 < r) :
    (∀ j : Fin r, observedPrimeEdgeLeg q m j = ⊤) ∧
      Function.Surjective (primeEdgeFormationBoundary r) ∧
      Module.finrank ℝ (PrimeEdgeFormationCharge r) = r - 1 := by
  refine ⟨fun j => observedPrimeEdgeLeg_eq_top hq0 hq1 m j,
    primeEdgeFormationBoundary_surjective hr,
    primeEdgeFormationCharge_finrank hr⟩

/-- Mean-zero representative of a packet. -/
def primeEdgeHarmonicProjection {r : ℕ} (hr : 0 < r)
    (x : PrimeEdgePacket r) : PrimeEdgeFormationCharge r :=
  ⟨finiteLabelCentered x, finiteLabelFusion_centered hr x⟩

@[simp] theorem primeEdgeHarmonicProjection_apply {r : ℕ} (hr : 0 < r)
    (x : PrimeEdgePacket r) (j : Fin r) :
    ((primeEdgeHarmonicProjection hr x : PrimeEdgeFormationCharge r) :
      PrimeEdgePacket r) j = x j - finiteLabelFusion x / (r : ℝ) :=
  rfl

/-- Endpoint plus harmonic component reconstruct every packet. -/
noncomputable def primeEdgePacketReconstruction {r : ℕ} (hr : 0 < r) :
    PrimeEdgePacket r ≃ₗ[ℝ] ℝ × PrimeEdgeFormationCharge r where
  toFun x := (finiteLabelFusion x, primeEdgeHarmonicProjection hr x)
  invFun sh := fun j => sh.2.1 j + sh.1 / (r : ℝ)
  left_inv x := by
    funext j
    change x j - finiteLabelFusion x / (r : ℝ) +
      finiteLabelFusion x / (r : ℝ) = x j
    ring
  right_inv sh := by
    rcases sh with ⟨s, h⟩
    apply Prod.ext
    · simp only [finiteLabelFusion, Finset.sum_add_distrib]
      have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp only [nsmul_eq_mul]
      have hh : ∑ i, (h : PrimeEdgePacket r) i = 0 := h.2
      rw [hh]
      field_simp
      ring
    · apply Subtype.ext
      funext j
      change ((h : PrimeEdgeFormationCharge r) : PrimeEdgePacket r) j + s / (r : ℝ) -
        finiteLabelFusion (fun i =>
          ((h : PrimeEdgeFormationCharge r) : PrimeEdgePacket r) i + s / (r : ℝ)) /
          (r : ℝ) = ((h : PrimeEdgeFormationCharge r) : PrimeEdgePacket r) j
      have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
      simp only [finiteLabelFusion, Finset.sum_add_distrib]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp only [nsmul_eq_mul]
      have hh : ∑ i, (h : PrimeEdgePacket r) i = 0 := h.2
      rw [hh]
      field_simp
      ring
  map_add' x y := by
    apply Prod.ext
    · simp [finiteLabelFusion, Finset.sum_add_distrib]
    · apply Subtype.ext
      funext j
      change (x j + y j) - finiteLabelFusion (x + y) / (r : ℝ) =
        (x j - finiteLabelFusion x / (r : ℝ)) +
          (y j - finiteLabelFusion y / (r : ℝ))
      rw [show finiteLabelFusion (x + y) = finiteLabelFusion x + finiteLabelFusion y by
        simp [finiteLabelFusion, Finset.sum_add_distrib]]
      ring
  map_smul' c x := by
    apply Prod.ext
    · simp [finiteLabelFusion, Finset.mul_sum]
    · apply Subtype.ext
      funext j
      change c * x j - finiteLabelFusion (c • x) / (r : ℝ) =
        c * (x j - finiteLabelFusion x / (r : ℝ))
      rw [show finiteLabelFusion (c • x) = c * finiteLabelFusion x by
        simp [finiteLabelFusion, Finset.mul_sum]]
      ring

/-- Euclidean squared norm of a finite packet. -/
def primeEdgePacketEnergy {r : ℕ} (x : PrimeEdgePacket r) : ℝ :=
  ∑ j, x j ^ 2

/-- Endpoint and harmonic charge obey exact Pythagorean conservation. -/
theorem primeEdge_packet_energy_conservation {r : ℕ} (hr : 0 < r)
    (x : PrimeEdgePacket r) :
    primeEdgePacketEnergy x =
      finiteLabelFusion x ^ 2 / (r : ℝ) +
        primeEdgePacketEnergy
          ((primeEdgeHarmonicProjection hr x : PrimeEdgeFormationCharge r) :
            PrimeEdgePacket r) := by
  classical
  simp only [primeEdgePacketEnergy, primeEdgeHarmonicProjection_apply,
    finiteLabelFusion]
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  let S : ℝ := ∑ i, x i
  have hexpand :
      (∑ j, (x j - S / (r : ℝ)) ^ 2) =
        ∑ j, (x j ^ 2 - 2 * x j * (S / (r : ℝ)) + (S / (r : ℝ)) ^ 2) := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hlinear : (∑ j, 2 * x j * (S / (r : ℝ))) =
      2 * S * (S / (r : ℝ)) := by
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, Finset.sum_mul]
  have hconst : (∑ _j : Fin r, (S / (r : ℝ)) ^ 2) =
      (r : ℝ) * (S / (r : ℝ)) ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp [nsmul_eq_mul]
  rw [hexpand, Finset.sum_add_distrib, Finset.sum_sub_distrib, hlinear, hconst]
  dsimp only [S]
  field_simp
  ring

/-- Coordinate adjoint of scalar fusion: a scalar is sent to the constant packet. -/
def primeEdgeFusionAdjoint (r : ℕ) : ℝ →ₗ[ℝ] PrimeEdgePacket r where
  toFun s := fun _ => s
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem primeEdgeFusionAdjoint_pairing {r : ℕ} (x : PrimeEdgePacket r) (s : ℝ) :
    (∑ j, x j * primeEdgeFusionAdjoint r s j) = finiteLabelFusion x * s := by
  simp [primeEdgeFusionAdjoint, finiteLabelFusion, Finset.sum_mul]

/-- Degree-zero Hodge Laplacian `Σ*Σ`. -/
def primeEdgeFormationLaplacian (r : ℕ) :
    PrimeEdgePacket r →ₗ[ℝ] PrimeEdgePacket r :=
  (primeEdgeFusionAdjoint r).comp (primeEdgeFormationBoundary r)

@[simp] theorem primeEdgeFormationLaplacian_apply {r : ℕ}
    (x : PrimeEdgePacket r) (j : Fin r) :
    primeEdgeFormationLaplacian r x j = finiteLabelFusion x := rfl

theorem primeEdgeFormationLaplacian_ker {r : ℕ} (hr : 0 < r) :
    LinearMap.ker (primeEdgeFormationLaplacian r) =
      LinearMap.ker (primeEdgeFormationBoundary r) := by
  ext x
  simp only [LinearMap.mem_ker]
  constructor
  · intro hx
    let j : Fin r := ⟨0, hr⟩
    have h := congrFun hx j
    change finiteLabelFusion x = 0
    exact h
  · intro hx
    funext j
    change finiteLabelFusion x = 0
    exact hx

theorem primeEdgeHarmonicProjection_mem_laplacian_ker {r : ℕ} (hr : 0 < r)
    (x : PrimeEdgePacket r) :
    (primeEdgeHarmonicProjection hr x : PrimeEdgePacket r) ∈
      LinearMap.ker (primeEdgeFormationLaplacian r) := by
  rw [primeEdgeFormationLaplacian_ker hr]
  exact (primeEdgeHarmonicProjection hr x).2

theorem primeEdgeHarmonicProjection_of_charge {r : ℕ} (hr : 0 < r)
    (h : PrimeEdgeFormationCharge r) :
    primeEdgeHarmonicProjection hr (h : PrimeEdgePacket r) = h := by
  apply Subtype.ext
  funext j
  rw [primeEdgeHarmonicProjection_apply]
  have hh : finiteLabelFusion (h : PrimeEdgePacket r) = 0 := h.2
  rw [hh]
  simp

theorem primeEdgeHarmonicProjection_idempotent {r : ℕ} (hr : 0 < r)
    (x : PrimeEdgePacket r) :
    primeEdgeHarmonicProjection hr
        ((primeEdgeHarmonicProjection hr x : PrimeEdgeFormationCharge r) :
          PrimeEdgePacket r) =
      primeEdgeHarmonicProjection hr x :=
  primeEdgeHarmonicProjection_of_charge hr (primeEdgeHarmonicProjection hr x)

theorem primeEdge_hodge_energy_eq_refinement_excess {r : ℕ} (hr : 0 < r)
    (x : PrimeEdgePacket r) :
    primeEdgePacketEnergy
        ((primeEdgeHarmonicProjection hr x : PrimeEdgeFormationCharge r) :
          PrimeEdgePacket r) =
      primeEdgePacketEnergy x - finiteLabelFusion x ^ 2 / (r : ℝ) := by
  rw [primeEdge_packet_energy_conservation hr x]
  ring

/-- Character-response packet on a finite aperture. -/
def primeEdgeResponsePacket (q : ℝ) (m r : ℕ) : PrimeEdgePacket r :=
  fun j => primeEdgeResponse q m j

/-- Reversal equivalence on finite edge labels. -/
def primeEdgeFinRevEquiv (r : ℕ) : Fin r ≃ Fin r where
  toFun := Fin.rev
  invFun := Fin.rev
  left_inv j := by simp
  right_inv j := by simp

/-- Signed functional-equation reversal of a packet. -/
def primeEdgeSignedReversal {r : ℕ} (x : PrimeEdgePacket r) : PrimeEdgePacket r :=
  fun j => -x (Fin.rev j)

/-- Reversal of the vertex basis. -/
def primeEdgeVertexReversal (r : ℕ) (x : Fin (r + 1) → ℝ) : Fin (r + 1) → ℝ :=
  fun k => x (Fin.rev k)

/-- Vertex reversal sends each oriented path edge to the negative reversed edge. -/
theorem primeEdgeVertexReversal_edge (r : ℕ) (j : Fin r) :
    primeEdgeVertexReversal r (primePathEdge r j) =
      -primePathEdge r (Fin.rev j) := by
  funext k
  change primePathEdge r j (Fin.rev k) = -primePathEdge r (Fin.rev j) k
  rw [primePathEdge_eq_primeExponentEdge, primePathEdge_eq_primeExponentEdge]
  simp only [primeExponentEdge]
  split_ifs <;> norm_num <;> simp [Fin.rev] at * <;> omega

/-- Signed reversal is an involutive linear equivalence. -/
def primeEdgeSignedReversalEquiv (r : ℕ) :
    PrimeEdgePacket r ≃ₗ[ℝ] PrimeEdgePacket r where
  toFun := primeEdgeSignedReversal
  invFun := primeEdgeSignedReversal
  left_inv x := by
    funext j
    simp [primeEdgeSignedReversal]
  right_inv x := by
    funext j
    simp [primeEdgeSignedReversal]
  map_add' x y := by
    funext j
    simp [primeEdgeSignedReversal]
    abel
  map_smul' c x := by
    funext j
    simp [primeEdgeSignedReversal]

theorem finiteLabelFusion_signedReversal {r : ℕ} (x : PrimeEdgePacket r) :
    finiteLabelFusion (primeEdgeSignedReversal x) = -finiteLabelFusion x := by
  have hreindex : (∑ j, x ((primeEdgeFinRevEquiv r) j)) = ∑ j, x j :=
    (primeEdgeFinRevEquiv r).sum_comp x
  simp only [finiteLabelFusion, primeEdgeSignedReversal, Finset.sum_neg_distrib]
  congr 1

/-- Signed reversal preserves the zero-sum formation carrier. -/
def primeEdgeChargeReversal (r : ℕ) :
    PrimeEdgeFormationCharge r ≃ₗ[ℝ] PrimeEdgeFormationCharge r where
  toFun x := ⟨primeEdgeSignedReversal (x : PrimeEdgePacket r), by
    change finiteLabelFusion (primeEdgeSignedReversal (x : PrimeEdgePacket r)) = 0
    rw [finiteLabelFusion_signedReversal]
    have hx : finiteLabelFusion (x : PrimeEdgePacket r) = 0 := x.2
    rw [hx, neg_zero]⟩
  invFun x := ⟨primeEdgeSignedReversal (x : PrimeEdgePacket r), by
    change finiteLabelFusion (primeEdgeSignedReversal (x : PrimeEdgePacket r)) = 0
    rw [finiteLabelFusion_signedReversal]
    have hx : finiteLabelFusion (x : PrimeEdgePacket r) = 0 := x.2
    rw [hx, neg_zero]⟩
  left_inv x := by
    apply Subtype.ext
    funext j
    simp [primeEdgeSignedReversal]
  right_inv x := by
    apply Subtype.ext
    funext j
    simp [primeEdgeSignedReversal]
  map_add' x y := by
    apply Subtype.ext
    funext j
    simp [primeEdgeSignedReversal]
    abel
  map_smul' c x := by
    apply Subtype.ext
    funext j
    simp [primeEdgeSignedReversal]

theorem primeEdgeHarmonicProjection_signedReversal {r : ℕ} (hr : 0 < r)
    (x : PrimeEdgePacket r) :
    primeEdgeHarmonicProjection hr (primeEdgeSignedReversal x) =
      primeEdgeChargeReversal r (primeEdgeHarmonicProjection hr x) := by
  apply Subtype.ext
  funext j
  change -x (Fin.rev j) -
      finiteLabelFusion (primeEdgeSignedReversal x) / (r : ℝ) =
    -(x (Fin.rev j) - finiteLabelFusion x / (r : ℝ))
  rw [finiteLabelFusion_signedReversal]
  ring

theorem primeEdgePacketEnergy_signedReversal {r : ℕ} (x : PrimeEdgePacket r) :
    primeEdgePacketEnergy (primeEdgeSignedReversal x) = primeEdgePacketEnergy x := by
  have hreindex : (∑ j, x ((primeEdgeFinRevEquiv r) j) ^ 2) = ∑ j, x j ^ 2 :=
    (primeEdgeFinRevEquiv r).sum_comp (fun j => x j ^ 2)
  change (∑ j, (-x (Fin.rev j)) ^ 2) = ∑ j, x j ^ 2
  simpa [primeEdgeFinRevEquiv] using hreindex

theorem primeEdgeChargeReversal_energy {r : ℕ} (h : PrimeEdgeFormationCharge r) :
    primeEdgePacketEnergy
        ((primeEdgeChargeReversal r h : PrimeEdgeFormationCharge r) : PrimeEdgePacket r) =
      primeEdgePacketEnergy (h : PrimeEdgePacket r) :=
  primeEdgePacketEnergy_signedReversal (h : PrimeEdgePacket r)

theorem primeEdgeChargeReversal_ne_zero {r : ℕ} {h : PrimeEdgeFormationCharge r}
    (hh : h ≠ 0) : primeEdgeChargeReversal r h ≠ 0 := by
  intro hs
  apply hh
  apply (primeEdgeChargeReversal r).injective
  simpa using hs

/-- On endpoint-plus-charge coordinates, reversal is `(s,h) ↦ (-s,Sh)`. -/
theorem primeEdgePacketReconstruction_signedReversal {r : ℕ} (hr : 0 < r)
    (x : PrimeEdgePacket r) :
    primeEdgePacketReconstruction hr (primeEdgeSignedReversal x) =
      (-finiteLabelFusion x,
        primeEdgeChargeReversal r (primeEdgeHarmonicProjection hr x)) := by
  apply Prod.ext
  · exact finiteLabelFusion_signedReversal x
  · exact primeEdgeHarmonicProjection_signedReversal hr x

/-- Reciprocal character execution is signed reversal up to one global metric-line factor. -/
theorem primeEdgeSignedReversal_response {q : ℝ} (hq : q ≠ 0) (m r : ℕ) :
    primeEdgeSignedReversal (primeEdgeResponsePacket q m r) =
      fun j => q ^ (2 * m + r) * primeEdgeResponse q⁻¹ m j := by
  funext j
  simp only [primeEdgeSignedReversal, primeEdgeResponsePacket, primeEdgeResponse]
  have hexp : 2 * m + r =
      (m + (Fin.rev j : ℕ)) + (m + (j : ℕ)) + 1 := by
    simp only [Fin.rev]
    omega
  rw [hexp, pow_add, pow_add, inv_pow]
  field_simp
  ring

/-- Literal two-edge Hodge charge at depth `m`. -/
def primeEdgeTwoEdgeHodgeCharge (q : ℝ) (m : ℕ) : ℝ :=
  (1 / 2 : ℝ) * q ^ (2 * m) * (1 - q) ^ 4

/-- Two-edge harmonic energy is the literal fourth-power charge. -/
theorem primeEdge_twoEdge_hodge_energy (q : ℝ) (m : ℕ) :
    primeEdgePacketEnergy
        ((primeEdgeHarmonicProjection (by omega : 0 < 2)
          (primeEdgeResponsePacket q m 2) : PrimeEdgeFormationCharge 2) :
            PrimeEdgePacket 2) =
      (1 / 2 : ℝ) * q ^ (2 * m) * (1 - q) ^ 4 := by
  simp only [primeEdgePacketEnergy, primeEdgeHarmonicProjection_apply,
    primeEdgeResponsePacket, finiteLabelFusion, Fin.sum_univ_two,
    primeEdgeResponse]
  norm_num [pow_succ]
  rw [show q ^ (2 * m) = (q ^ m) ^ 2 by rw [mul_comm, pow_mul]]
  ring

theorem primeEdge_twoEdge_hodge_energy_eq_zero_iff {q : ℝ} (hq : 0 < q) (m : ℕ) :
    primeEdgePacketEnergy
        ((primeEdgeHarmonicProjection (by omega : 0 < 2)
          (primeEdgeResponsePacket q m 2) : PrimeEdgeFormationCharge 2) :
            PrimeEdgePacket 2) = 0 ↔ q = 1 := by
  rw [primeEdge_twoEdge_hodge_energy]
  have hpow : q ^ (2 * m) ≠ 0 := pow_ne_zero _ (ne_of_gt hq)
  have hfac : (1 / 2 : ℝ) * q ^ (2 * m) ≠ 0 := mul_ne_zero (by norm_num) hpow
  constructor
  · intro h
    have hfour : (1 - q) ^ 4 = 0 := (mul_eq_zero.mp h).resolve_left hfac
    have hsub : 1 - q = 0 := by
      by_contra hne
      exact pow_ne_zero 4 hne hfour
    linarith
  · rintro rfl
    norm_num

theorem primeEdgeTwoEdgeHodgeCharge_eq_zero_iff {q : ℝ} (hq : 0 < q) (m : ℕ) :
    primeEdgeTwoEdgeHodgeCharge q m = 0 ↔ q = 1 := by
  simp only [primeEdgeTwoEdgeHodgeCharge]
  rw [← primeEdge_twoEdge_hodge_energy]
  exact primeEdge_twoEdge_hodge_energy_eq_zero_iff hq m

theorem primeRadial_twoEdge_hodge_energy_eq_zero_iff
    {p : ℕ} (hp : p.Prime) {ν : ℝ} (m : ℕ) :
    primeEdgePacketEnergy
        ((primeEdgeHarmonicProjection (by omega : 0 < 2)
          (primeEdgeResponsePacket ((p : ℝ) ^ ν) m 2) : PrimeEdgeFormationCharge 2) :
            PrimeEdgePacket 2) = 0 ↔ ν = 0 := by
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  rw [primeEdge_twoEdge_hodge_energy_eq_zero_iff (Real.rpow_pos_of_pos hp0 ν)]
  have hp1 : (p : ℝ) ≠ 1 := by exact_mod_cast hp.ne_one
  simpa using (Real.rpow_right_inj hp0 hp1 (y := ν) (z := 0))

/-- Euclidean `ℓ¹` variation of a packet. -/
def primeEdgePacketVariation {r : ℕ} (x : PrimeEdgePacket r) : ℝ :=
  ∑ j, |x j|

theorem abs_primeEdgeResponse_neg_one (m : ℕ) {r : ℕ} (j : Fin r) :
    |primeEdgeResponse (-1) m j| = 2 := by
  have hnorm := norm_complexCharacterEdge_neg_one (m + (j : ℕ))
  have heq := primeEdgeResponse_eq_characterEdge (-1) m j
  have heq' :
      (primeEdgeResponse (-1) m j : ℂ) =
        complexCharacterEdge (-1) (m + (j : ℕ)) := by
    simpa using heq
  calc
    |primeEdgeResponse (-1) m j| = ‖(primeEdgeResponse (-1) m j : ℂ)‖ := by simp
    _ = ‖complexCharacterEdge (-1) (m + (j : ℕ))‖ := congrArg norm heq'
    _ = 2 := hnorm

theorem primeEdgeResponse_neg_one_energy (m r : ℕ) :
    primeEdgePacketEnergy (primeEdgeResponsePacket (-1) m r) = 4 * r := by
  simp only [primeEdgePacketEnergy, primeEdgeResponsePacket]
  calc
    ∑ j : Fin r, primeEdgeResponse (-1) m j ^ 2 = ∑ _j : Fin r, (4 : ℝ) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← sq_abs, abs_primeEdgeResponse_neg_one]
      norm_num
    _ = 4 * r := by simp; ring

theorem primeEdgeResponse_neg_one_variation (m r : ℕ) :
    primeEdgePacketVariation (primeEdgeResponsePacket (-1) m r) = 2 * r := by
  simp [primeEdgePacketVariation, primeEdgeResponsePacket,
    abs_primeEdgeResponse_neg_one]
  ring

theorem primeEdgeResponse_neg_one_even_fusion (m n : ℕ) :
    finiteLabelFusion (primeEdgeResponsePacket (-1) m (2 * n)) = 0 := by
  have hfin :
      (∑ j : Fin (2 * n), complexCharacterEdge (-1) (m + (j : ℕ))) = 0 := by
    rw [Fin.sum_univ_eq_sum_range
      (fun j : ℕ => complexCharacterEdge (-1) (m + j)) (2 * n)]
    exact sum_complexCharacterEdge_neg_one_even m n
  have hcast :
      (∑ j : Fin (2 * n), (primeEdgeResponse (-1) m j : ℂ)) = 0 := by
    calc
      (∑ j : Fin (2 * n), (primeEdgeResponse (-1) m j : ℂ)) =
          ∑ j : Fin (2 * n), complexCharacterEdge (-1) (m + (j : ℕ)) := by
        apply Finset.sum_congr rfl
        intro j _
        simpa using primeEdgeResponse_eq_characterEdge (-1) m j
      _ = 0 := hfin
  exact_mod_cast hcast

theorem primeEdgeResponse_neg_one_even_harmonic (m n : ℕ) :
    ((primeEdgeHarmonicProjection (by omega : 0 < 2 * (n + 1))
        (primeEdgeResponsePacket (-1) m (2 * (n + 1))) :
          PrimeEdgeFormationCharge (2 * (n + 1))) : PrimeEdgePacket (2 * (n + 1))) =
      primeEdgeResponsePacket (-1) m (2 * (n + 1)) := by
  funext j
  rw [primeEdgeHarmonicProjection_apply,
    primeEdgeResponse_neg_one_even_fusion]
  simp

/-- Even recurrent apertures close at the endpoint but retain linearly growing Hodge energy. -/
theorem primeEdge_recurrent_even_hodge_ledger (m n : ℕ) :
    finiteLabelFusion (primeEdgeResponsePacket (-1) m (2 * n)) = 0 ∧
      primeEdgePacketEnergy (primeEdgeResponsePacket (-1) m (2 * n)) = 8 * n ∧
      primeEdgePacketVariation (primeEdgeResponsePacket (-1) m (2 * n)) = 4 * n := by
  refine ⟨primeEdgeResponse_neg_one_even_fusion m n, ?_, ?_⟩
  · rw [primeEdgeResponse_neg_one_energy]
    norm_num [Nat.cast_mul]
    ring
  · rw [primeEdgeResponse_neg_one_variation]
    norm_num [Nat.cast_mul]
    ring

theorem primeEdgeTwoEdgeHodgeCharge_eq_geometric (q : ℝ) (m : ℕ) :
    primeEdgeTwoEdgeHodgeCharge q m =
      ((q - 1) ^ 2 / 2) * geometricRefinementEnergy q m := by
  simp only [primeEdgeTwoEdgeHodgeCharge]
  rw [geometricRefinementEnergy_eq,
    show q ^ (2 * m) = (q ^ 2) ^ m by rw [pow_mul]]
  ring

theorem bilateral_primeEdgeTwoEdgeHodgeCharge_summable_iff {q : ℝ} (hq : 0 < q) :
    (Summable (primeEdgeTwoEdgeHodgeCharge q) ∧
        Summable (primeEdgeTwoEdgeHodgeCharge q⁻¹)) ↔ q = 1 := by
  by_cases hq1 : q = 1
  · subst q
    constructor
    · intro _
      rfl
    · intro _
      constructor <;> convert (summable_zero : Summable (fun _ : ℕ => (0 : ℝ))) using 1 <;>
        funext n <;> simp [primeEdgeTwoEdgeHodgeCharge]
  · have hc : (q - 1) ^ 2 / 2 ≠ 0 := div_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hq1))
      (by norm_num)
    have hqi1 : q⁻¹ ≠ 1 := by
      intro hi
      apply hq1
      have := congrArg Inv.inv hi
      simpa using this
    have hci : (q⁻¹ - 1) ^ 2 / 2 ≠ 0 :=
      div_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hqi1)) (by norm_num)
    rw [show primeEdgeTwoEdgeHodgeCharge q =
        fun n => ((q - 1) ^ 2 / 2) * geometricRefinementEnergy q n by
      funext n
      exact primeEdgeTwoEdgeHodgeCharge_eq_geometric q n]
    rw [show primeEdgeTwoEdgeHodgeCharge q⁻¹ =
        fun n => ((q⁻¹ - 1) ^ 2 / 2) * geometricRefinementEnergy q⁻¹ n by
      funext n
      exact primeEdgeTwoEdgeHodgeCharge_eq_geometric q⁻¹ n]
    rw [summable_mul_left_iff hc, summable_mul_left_iff hci]
    exact bilateral_geometricRefinementEnergy_summable_iff hq

theorem all_primeEdgeTwoEdgeHodgeCharge_eq_zero_iff {q : ℝ} (hq : 0 < q) :
    (∀ m, primeEdgeTwoEdgeHodgeCharge q m = 0) ↔ q = 1 := by
  constructor
  · intro h
    exact (primeEdgeTwoEdgeHodgeCharge_eq_zero_iff hq 0).mp (h 0)
  · rintro rfl m
    simp [primeEdgeTwoEdgeHodgeCharge]

/-- Cofinal Hodge history beginning at source depth `M`. -/
def cofinalPrimeEdgeTwoEdgeHodgeCharge (q : ℝ) (M n : ℕ) : ℝ :=
  primeEdgeTwoEdgeHodgeCharge q (M + n)

theorem cofinalPrimeEdgeTwoEdgeHodgeCharge_eq (q : ℝ) (M n : ℕ) :
    cofinalPrimeEdgeTwoEdgeHodgeCharge q M n =
      q ^ (2 * M) * primeEdgeTwoEdgeHodgeCharge q n := by
  simp only [cofinalPrimeEdgeTwoEdgeHodgeCharge, primeEdgeTwoEdgeHodgeCharge]
  rw [Nat.mul_add, pow_add]
  ring

theorem bilateral_cofinalPrimeEdgeTwoEdgeHodgeCharge_summable_iff
    {q : ℝ} (hq : 0 < q) (M : ℕ) :
    (Summable (cofinalPrimeEdgeTwoEdgeHodgeCharge q M) ∧
        Summable (cofinalPrimeEdgeTwoEdgeHodgeCharge q⁻¹ M)) ↔ q = 1 := by
  have hq0 : q ^ (2 * M) ≠ 0 := pow_ne_zero _ (ne_of_gt hq)
  have hqi0 : q⁻¹ ^ (2 * M) ≠ 0 := pow_ne_zero _ (inv_ne_zero (ne_of_gt hq))
  rw [show cofinalPrimeEdgeTwoEdgeHodgeCharge q M =
      fun n => q ^ (2 * M) * primeEdgeTwoEdgeHodgeCharge q n by
    funext n
    exact cofinalPrimeEdgeTwoEdgeHodgeCharge_eq q M n]
  rw [show cofinalPrimeEdgeTwoEdgeHodgeCharge q⁻¹ M =
      fun n => q⁻¹ ^ (2 * M) * primeEdgeTwoEdgeHodgeCharge q⁻¹ n by
    funext n
    exact cofinalPrimeEdgeTwoEdgeHodgeCharge_eq q⁻¹ M n]
  rw [summable_mul_left_iff hq0, summable_mul_left_iff hqi0]
  exact bilateral_primeEdgeTwoEdgeHodgeCharge_summable_iff hq

/-- Global bilateral properness and pointwise vanishing select the same unit character. -/
theorem primeEdge_global_properness_selector {q : ℝ} (hq : 0 < q) (M : ℕ) :
    ((Summable (cofinalPrimeEdgeTwoEdgeHodgeCharge q M) ∧
        Summable (cofinalPrimeEdgeTwoEdgeHodgeCharge q⁻¹ M)) ↔ q = 1) ∧
      (q = 1 ↔ ∀ m, primeEdgeTwoEdgeHodgeCharge q m = 0) := by
  exact ⟨bilateral_cofinalPrimeEdgeTwoEdgeHodgeCharge_summable_iff hq M,
    (all_primeEdgeTwoEdgeHodgeCharge_eq_zero_iff hq).symm⟩

theorem primeRadial_bilateral_cofinalHodgeCharge_summable_iff
    {p : ℕ} (hp : p.Prime) {ν : ℝ} (M : ℕ) :
    (Summable (cofinalPrimeEdgeTwoEdgeHodgeCharge ((p : ℝ) ^ ν) M) ∧
        Summable (cofinalPrimeEdgeTwoEdgeHodgeCharge (((p : ℝ) ^ ν)⁻¹) M)) ↔
      ν = 0 := by
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  rw [bilateral_cofinalPrimeEdgeTwoEdgeHodgeCharge_summable_iff
    (Real.rpow_pos_of_pos hp0 ν)]
  have hp1 : (p : ℝ) ≠ 1 := by exact_mod_cast hp.ne_one
  simpa using (Real.rpow_right_inj hp0 hp1 (y := ν) (z := 0))

/-- Depth-`12` differential independence coexists with arbitrarily large formation charge. -/
theorem rankTwelve_differentialIndependent_and_unbounded_primeEdgeFormation :
    DifferentialIndependent zetaUpperEndDifferentialField
        (fun j => finiteAbscissaLSeriesToUpperEndMero
          (completeResolutionNormalizedFiniteAbscissaSource 12 j)) ∧
      ∀ N : ℕ, ∃ r : ℕ, Module.finrank ℝ (PrimeEdgeFormationCharge r) = N := by
  refine ⟨rankTwelveFiniteAbscissaSource_relativeDifferentialIndependent, ?_⟩
  intro N
  refine ⟨N + 1, ?_⟩
  rw [primeEdgeFormationCharge_finrank (by omega)]
  omega

end

end GaloisForLFunctions.HTGeometry
