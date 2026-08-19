import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

open Complex Set Filter Topology
open scoped InnerProduct LinearPMap

noncomputable section

namespace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem symmetric_isClosable {S : H →ₗ.[ℂ] H}
    (hDense : Dense (S.domain : Set H)) (hSymm : S.IsFormalAdjoint S) :
    S.IsClosable := by
  exact isClosable_iff_exists_closed_extension.mpr
    ⟨S.adjoint, adjoint_isClosed hDense, hSymm.le_adjoint hDense⟩

theorem closure_adjoint_eq_adjoint {S : H →ₗ.[ℂ] H}
    (hDense : Dense (S.domain : Set H)) (hSymm : S.IsFormalAdjoint S) :
    S.closure.adjoint = S.adjoint := by
  let hClose : S.IsClosable := symmetric_isClosable hDense hSymm
  have hSC : S ≤ S.closure := S.le_closure
  have hDenseC : Dense (S.closure.domain : Set H) :=
    hDense.mono hSC.1
  have hGraph : _root_.closure (S.graph : Set (H × H)) = S.closure.graph := by
    rw [← Submodule.topologicalClosure_coe]
    exact congrArg SetLike.coe hClose.graph_closure_eq_closure_graph
  apply eq_of_eq_graph
  ext p
  simp only [mem_graph_iff, Subtype.exists, exists_and_left, exists_eq_left]
  constructor
  · rintro ⟨hp, hout⟩
    have hpS : p.fst ∈ S.adjoint.domain := by
      apply mem_adjoint_domain_of_exists
      refine ⟨p.snd, ?_⟩
      intro x
      let xC : S.closure.domain := ⟨(x : H), hSC.1 x.property⟩
      have hxapp : S x = S.closure xC := hSC.2 rfl
      let yC : S.closure.adjoint.domain := ⟨p.fst, hp⟩
      calc
        inner ℂ p.snd (x : H) = inner ℂ (S.closure.adjoint yC) (xC : H) := by rw [hout]
        _ = inner ℂ p.fst (S.closure xC) :=
          adjoint_isFormalAdjoint hDenseC yC xC
        _ = inner ℂ p.fst (S x) := by rw [hxapp]
    refine ⟨hpS, ?_⟩
    apply hDense.eq_of_inner_left ℂ
    intro x hx
    let xS : S.domain := ⟨x, hx⟩
    let xC : S.closure.domain := ⟨x, hSC.1 hx⟩
    let yS : S.adjoint.domain := ⟨p.fst, hpS⟩
    let yC : S.closure.adjoint.domain := ⟨p.fst, hp⟩
    have hxapp : S xS = S.closure xC := hSC.2 rfl
    calc
      inner ℂ (S.adjoint yS) x = inner ℂ p.fst (S xS) :=
        adjoint_isFormalAdjoint hDense yS xS
      _ = inner ℂ p.fst (S.closure xC) := by rw [hxapp]
      _ = inner ℂ (S.closure.adjoint yC) x :=
        (adjoint_isFormalAdjoint hDenseC yC xC).symm
      _ = inner ℂ p.snd x := by rw [hout]
  · rintro ⟨hp, hout⟩
    have hpair : ∀ x : S.domain,
        inner ℂ p.snd (x : H) = inner ℂ p.fst (S x) := by
      intro x
      let yS : S.adjoint.domain := ⟨p.fst, hp⟩
      calc
        inner ℂ p.snd (x : H) = inner ℂ (S.adjoint yS) (x : H) := by rw [hout]
        _ = inner ℂ p.fst (S x) := adjoint_isFormalAdjoint hDense yS x
    have hpairC : ∀ x : S.closure.domain,
        inner ℂ p.snd (x : H) = inner ℂ p.fst (S.closure x) := by
      intro x
      let Z : Set (H × H) :=
        {q | inner ℂ p.snd q.1 = inner ℂ p.fst q.2}
      have hZclosed : _root_.IsClosed Z := by
        apply isClosed_eq <;> fun_prop
      have hSgraph : (S.graph : Set (H × H)) ⊆ Z := by
        intro q hq
        change q ∈ S.graph at hq
        rw [mem_graph_iff] at hq
        obtain ⟨z, hz1, hz2⟩ := hq
        change inner ℂ p.snd q.1 = inner ℂ p.fst q.2
        rw [← hz1, ← hz2]
        exact hpair z
      have hxgraph : ((x : H), S.closure x) ∈ S.closure.graph := by
        rw [mem_graph_iff]
        exact ⟨x, rfl, rfl⟩
      have hxclosure : ((x : H), S.closure x) ∈
          _root_.closure (S.graph : Set (H × H)) := by
        rw [hGraph]
        exact hxgraph
      exact closure_minimal hSgraph hZclosed hxclosure
    have hpC : p.fst ∈ S.closure.adjoint.domain := by
      apply mem_adjoint_domain_of_exists
      exact ⟨p.snd, hpairC⟩
    refine ⟨hpC, ?_⟩
    exact adjoint_apply_eq hDenseC ⟨p.fst, hpC⟩ hpairC

theorem exists_closure_add_deficiencies {S : H →ₗ.[ℂ] H}
    (hDense : Dense (S.domain : Set H)) (hSymm : S.IsFormalAdjoint S)
    (y : S.adjoint.domain) :
    ∃ x : S.closure.domain, ∃ p m : S.adjoint.domain,
      S.adjoint p = I • (p : H) ∧
      S.adjoint m = (-I) • (m : H) ∧
      (y : H) = (x : H) + (p : H) + (m : H) := by
  let hClose : S.IsClosable := symmetric_isClosable hDense hSymm
  let C := S.closure
  have hCclosed : C.IsClosed := hClose.closure_isClosed
  have hSC : S ≤ C := S.le_closure
  have hCSadj : C ≤ S.adjoint := by
    have hAdjClosed : S.adjoint.IsClosed := adjoint_isClosed hDense
    have hAdjClosure : S.adjoint.closure = S.adjoint := by
      apply eq_of_eq_graph
      rw [← hAdjClosed.isClosable.graph_closure_eq_closure_graph]
      exact hAdjClosed.submodule_topologicalClosure_eq
    calc
      C = S.closure := rfl
      _ ≤ S.adjoint.closure := hAdjClosed.isClosable.closure_mono (hSymm.le_adjoint hDense)
      _ = S.adjoint := hAdjClosure
  have hAdjEq : C.adjoint = S.adjoint := closure_adjoint_eq_adjoint hDense hSymm
  have hGraphClosed : _root_.IsClosed (C.graph : Set (H × H)) := hCclosed
  let P := WithLp 2 (H × H)
  let e : P ≃ₗ[ℂ] H × H := WithLp.linearEquiv 2 ℂ (H × H)
  let G : Submodule ℂ P := C.graph.comap e.toLinearMap
  have hGclosed : _root_.IsClosed (G : Set P) := by
    change _root_.IsClosed
      ((WithLp.homeomorphProd 2 H H) ⁻¹' (C.graph : Set (H × H)))
    exact hGraphClosed.preimage (WithLp.homeomorphProd 2 H H).continuous
  letI : CompleteSpace G := hGclosed.completeSpace_coe
  let gy : P := WithLp.toLp 2 ((y : H), S.adjoint y)
  obtain ⟨q, hq, r, hr, hsum⟩ := G.exists_add_mem_mem_orthogonal gy
  change e q ∈ C.graph at hq
  rw [mem_graph_iff] at hq
  obtain ⟨x, hxq1, hxq2⟩ := hq
  let xC : C.domain := x
  have hxval : (xC : H) = q.fst := by
    change (xC : H) = (e q).1
    exact hxq1
  have hxapp : C xC = q.snd := by
    change C xC = (e q).2
    exact hxq2
  have hyr1 : (y : H) = (xC : H) + r.fst := by
    have := congrArg WithLp.fst hsum
    rw [WithLp.add_fst] at this
    simpa [gy, hxval] using this
  have hyr2 : S.adjoint y = C xC + r.snd := by
    have := congrArg WithLp.snd hsum
    rw [WithLp.add_snd] at this
    simpa [gy, hxapp] using this
  have hxAdjMem : (xC : H) ∈ S.adjoint.domain := hCSadj.1 xC.property
  let xAdj : S.adjoint.domain := ⟨(xC : H), hxAdjMem⟩
  have hxAdjApp : S.adjoint xAdj = C xC := (hCSadj.2 rfl).symm
  have hruMem : r.fst ∈ S.adjoint.domain := by
    have hrsub : r.fst = (y : H) - (xC : H) := by rw [hyr1]; module
    rw [hrsub]
    exact S.adjoint.domain.sub_mem y.property hxAdjMem
  let ru : S.adjoint.domain := ⟨r.fst, hruMem⟩
  have hruApp : S.adjoint ru = r.snd := by
    have hrsub : ru = y - xAdj := by
      apply Subtype.ext
      dsimp [ru, xAdj]
      rw [hyr1]
      module
    rw [hrsub, map_sub, hxAdjApp, hyr2]
    module
  have hrvCAdj : r.snd ∈ C.adjoint.domain := by
    apply mem_adjoint_domain_of_exists
    refine ⟨-r.fst, ?_⟩
    intro z
    have horth := hr (WithLp.toLp 2 ((z : H), C z)) (by
      change e (WithLp.toLp 2 ((z : H), C z)) ∈ C.graph
      rw [mem_graph_iff]
      exact ⟨z, rfl, rfl⟩)
    have horth' : inner ℂ r (WithLp.toLp 2 ((z : H), C z)) = 0 := by
      calc
        inner ℂ r (WithLp.toLp 2 ((z : H), C z)) =
            star (inner ℂ (WithLp.toLp 2 ((z : H), C z)) r) :=
          (inner_conj_symm r _).symm
        _ = 0 := by rw [horth]; simp
    rw [WithLp.prod_inner_apply] at horth'
    change inner ℂ r.fst (z : H) + inner ℂ r.snd (C z) = 0 at horth'
    rw [inner_neg_left]
    linear_combination -horth'
  have hrvAdj : r.snd ∈ S.adjoint.domain := by
    rw [← hAdjEq]
    exact hrvCAdj
  let rv : S.adjoint.domain := ⟨r.snd, hrvAdj⟩
  have hrvAppC : C.adjoint ⟨r.snd, hrvCAdj⟩ = -r.fst := by
    apply adjoint_apply_eq (hDense.mono hSC.1)
    intro z
    have horth := hr (WithLp.toLp 2 ((z : H), C z)) (by
      change e (WithLp.toLp 2 ((z : H), C z)) ∈ C.graph
      rw [mem_graph_iff]
      exact ⟨z, rfl, rfl⟩)
    have horth' : inner ℂ r (WithLp.toLp 2 ((z : H), C z)) = 0 := by
      calc
        inner ℂ r (WithLp.toLp 2 ((z : H), C z)) =
            star (inner ℂ (WithLp.toLp 2 ((z : H), C z)) r) :=
          (inner_conj_symm r _).symm
        _ = 0 := by rw [horth]; simp
    rw [WithLp.prod_inner_apply] at horth'
    change inner ℂ r.fst (z : H) + inner ℂ r.snd (C z) = 0 at horth'
    rw [inner_neg_left]
    change -inner ℂ r.fst (z : H) = inner ℂ r.snd (C z)
    linear_combination -horth'
  have hrvApp : S.adjoint rv = -r.fst := by
    have hpC : (r.snd, -r.fst) ∈ C.adjoint.graph := by
      rw [mem_graph_iff]
      exact ⟨⟨r.snd, hrvCAdj⟩, rfl, hrvAppC⟩
    have hpS : (r.snd, -r.fst) ∈ S.adjoint.graph := by
      rw [← hAdjEq]
      exact hpC
    rw [mem_graph_iff] at hpS
    obtain ⟨z, hzval, hzapp⟩ := hpS
    have hzrv : z = rv := Subtype.ext hzval
    simpa [hzrv] using hzapp
  let pH : H := (1 / 2 : ℂ) • ((ru : H) - I • (rv : H))
  let mH : H := (1 / 2 : ℂ) • ((ru : H) + I • (rv : H))
  have hpMem : pH ∈ S.adjoint.domain := by
    exact S.adjoint.domain.smul_mem _
      (S.adjoint.domain.sub_mem ru.property (S.adjoint.domain.smul_mem _ rv.property))
  have hmMem : mH ∈ S.adjoint.domain := by
    exact S.adjoint.domain.smul_mem _
      (S.adjoint.domain.add_mem ru.property (S.adjoint.domain.smul_mem _ rv.property))
  let p : S.adjoint.domain := ⟨pH, hpMem⟩
  let m : S.adjoint.domain := ⟨mH, hmMem⟩
  have hIcoef : (I * (1 / 2 : ℂ)) * I = -(1 / 2 : ℂ) := by
    calc
      _ = (I * I) * (1 / 2 : ℂ) := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  have hnegIcoef : ((-I) * (1 / 2 : ℂ)) * I = (1 / 2 : ℂ) := by
    calc
      _ = -((I * I) * (1 / 2 : ℂ)) := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  refine ⟨xC, p, m, ?_, ?_, ?_⟩
  · change S.adjoint
      ((1 / 2 : ℂ) • (ru - I • rv)) = I • pH
    rw [map_smul, map_sub, map_smul, hruApp, hrvApp]
    dsimp [pH]
    change (1 / 2 : ℂ) • ((rv : H) - I • (-(ru : H))) =
      I • ((1 / 2 : ℂ) • ((ru : H) - I • (rv : H)))
    calc
      _ = (1 / 2 : ℂ) • (rv : H) + (I * (1 / 2 : ℂ)) • (ru : H) := by
        module
      _ = _ := by
        rw [smul_smul, smul_sub, smul_smul, hIcoef]
        module
  · change S.adjoint
      ((1 / 2 : ℂ) • (ru + I • rv)) = (-I) • mH
    rw [map_smul, map_add, map_smul, hruApp, hrvApp]
    dsimp [mH]
    change (1 / 2 : ℂ) • ((rv : H) + I • (-(ru : H))) =
      (-I) • ((1 / 2 : ℂ) • ((ru : H) + I • (rv : H)))
    calc
      _ = (1 / 2 : ℂ) • (rv : H) + ((-I) * (1 / 2 : ℂ)) • (ru : H) := by
        module
      _ = _ := by
        rw [smul_smul, smul_add, smul_smul, hnegIcoef]
        module
  · rw [hyr1]
    dsimp [p, m, pH, mH, ru]
    module

theorem closure_le_adjoint {S : H →ₗ.[ℂ] H}
    (hDense : Dense (S.domain : Set H)) (hSymm : S.IsFormalAdjoint S) :
    S.closure ≤ S.adjoint := by
  have hAdjClosed : S.adjoint.IsClosed := adjoint_isClosed hDense
  have hAdjClosure : S.adjoint.closure = S.adjoint := by
    apply eq_of_eq_graph
    rw [← hAdjClosed.isClosable.graph_closure_eq_closure_graph]
    exact hAdjClosed.submodule_topologicalClosure_eq
  calc
    S.closure ≤ S.adjoint.closure :=
      hAdjClosed.isClosable.closure_mono (hSymm.le_adjoint hDense)
    _ = S.adjoint := hAdjClosure

def deficiencyBoundaryVector {S : H →ₗ.[ℂ] H}
    (p m : S.adjoint.domain) (u : ℂ) : H :=
  (p : H) + u • (m : H)

def deficiencyExtensionDomain {S : H →ₗ.[ℂ] H}
    (p m : S.adjoint.domain) (u : ℂ) : Submodule ℂ H :=
  S.closure.domain ⊔ ℂ ∙ deficiencyBoundaryVector p m u

theorem deficiencyExtensionDomain_le_adjoint {S : H →ₗ.[ℂ] H}
    (hDense : Dense (S.domain : Set H)) (hSymm : S.IsFormalAdjoint S)
    (p m : S.adjoint.domain) (u : ℂ) :
    deficiencyExtensionDomain p m u ≤ S.adjoint.domain := by
  rw [deficiencyExtensionDomain, sup_le_iff]
  constructor
  · exact (closure_le_adjoint hDense hSymm).1
  · rw [Submodule.span_le]
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    rw [hx]
    exact S.adjoint.domain.add_mem p.property
      (S.adjoint.domain.smul_mem u m.property)

noncomputable def deficiencyExtension {S : H →ₗ.[ℂ] H}
    (hDense : Dense (S.domain : Set H)) (hSymm : S.IsFormalAdjoint S)
    (p m : S.adjoint.domain) (u : ℂ) : H →ₗ.[ℂ] H where
  domain := deficiencyExtensionDomain p m u
  toFun := S.adjoint.toFun.comp
    (Submodule.inclusion (deficiencyExtensionDomain_le_adjoint hDense hSymm p m u))

@[simp] theorem deficiencyExtension_domain {S : H →ₗ.[ℂ] H}
    (hDense : Dense (S.domain : Set H)) (hSymm : S.IsFormalAdjoint S)
    (p m : S.adjoint.domain) (u : ℂ) :
    (deficiencyExtension hDense hSymm p m u).domain =
      deficiencyExtensionDomain p m u := rfl

theorem deficiencyExtension_apply {S : H →ₗ.[ℂ] H}
    (hDense : Dense (S.domain : Set H)) (hSymm : S.IsFormalAdjoint S)
    (p m : S.adjoint.domain) (u : ℂ)
    (x : (deficiencyExtension hDense hSymm p m u).domain) :
    deficiencyExtension hDense hSymm p m u x =
      S.adjoint ⟨(x : H), deficiencyExtensionDomain_le_adjoint hDense hSymm p m u x.property⟩ :=
  rfl

theorem deficiencyExtension_le_adjoint {S : H →ₗ.[ℂ] H}
    (hDense : Dense (S.domain : Set H)) (hSymm : S.IsFormalAdjoint S)
    (p m : S.adjoint.domain) (u : ℂ) :
    deficiencyExtension hDense hSymm p m u ≤ S.adjoint := by
  constructor
  · exact deficiencyExtensionDomain_le_adjoint hDense hSymm p m u
  · intro x y hxy
    change S.adjoint
      ⟨(x : H), deficiencyExtensionDomain_le_adjoint hDense hSymm p m u x.property⟩ =
        S.adjoint y
    apply congrArg S.adjoint
    exact Subtype.ext hxy

theorem le_deficiencyExtension {S : H →ₗ.[ℂ] H}
    (hDense : Dense (S.domain : Set H)) (hSymm : S.IsFormalAdjoint S)
    (p m : S.adjoint.domain) (u : ℂ) :
    S ≤ deficiencyExtension hDense hSymm p m u := by
  let A := deficiencyExtension hDense hSymm p m u
  have hSC : S ≤ S.closure := S.le_closure
  have hSA : S.domain ≤ A.domain := by
    intro x hx
    change x ∈ S.closure.domain ⊔ ℂ ∙ deficiencyBoundaryVector p m u
    exact Submodule.mem_sup_left (hSC.1 hx)
  refine ⟨hSA, ?_⟩
  intro x y hxy
  have hSAdj := hSymm.le_adjoint hDense
  let yAdj : S.adjoint.domain :=
    ⟨(y : H), deficiencyExtensionDomain_le_adjoint hDense hSymm p m u y.property⟩
  change S x = S.adjoint
    ⟨(y : H), deficiencyExtensionDomain_le_adjoint hDense hSymm p m u
      y.property⟩
  exact hSAdj.2 hxy

theorem exists_closure_add_smul_boundary {S : H →ₗ.[ℂ] H}
    (p m : S.adjoint.domain) (u : ℂ)
    {x : H} (hx : x ∈ deficiencyExtensionDomain p m u) :
    ∃ c : S.closure.domain, ∃ q : ℂ,
      x = (c : H) + q • deficiencyBoundaryVector p m u := by
  rw [deficiencyExtensionDomain, Submodule.mem_sup] at hx
  obtain ⟨c, hc, w, hw, hsum⟩ := hx
  rw [Submodule.mem_span_singleton] at hw
  obtain ⟨q, hq⟩ := hw
  refine ⟨⟨c, hc⟩, q, ?_⟩
  rw [← hq] at hsum
  exact hsum.symm

def adjointBoundaryPairing (S : H →ₗ.[ℂ] H)
    (x y : S.adjoint.domain) : ℂ :=
  inner ℂ (S.adjoint x) (y : H) - inner ℂ (x : H) (S.adjoint y)

theorem adjoint_pairing_closure_right {S : H →ₗ.[ℂ] H}
    (hDense : Dense (S.domain : Set H)) (hSymm : S.IsFormalAdjoint S)
    (x : S.adjoint.domain) (c : S.closure.domain) :
    inner ℂ (S.adjoint x) (c : H) = inner ℂ (x : H) (S.closure c) := by
  have hAdjEq := closure_adjoint_eq_adjoint hDense hSymm
  have hpS : ((x : H), S.adjoint x) ∈ S.adjoint.graph := by
    rw [mem_graph_iff]
    exact ⟨x, rfl, rfl⟩
  have hpC : ((x : H), S.adjoint x) ∈ S.closure.adjoint.graph := by
    rw [hAdjEq]
    exact hpS
  rw [mem_graph_iff] at hpC
  obtain ⟨xC, hxval, hxapp⟩ := hpC
  have hDenseC : Dense (S.closure.domain : Set H) :=
    hDense.mono S.le_closure.1
  have hformal := adjoint_isFormalAdjoint hDenseC xC c
  rw [hxval, hxapp] at hformal
  simpa using hformal

theorem adjoint_pairing_closure_left {S : H →ₗ.[ℂ] H}
    (hDense : Dense (S.domain : Set H)) (hSymm : S.IsFormalAdjoint S)
    (c : S.closure.domain) (x : S.adjoint.domain) :
    inner ℂ (S.closure c) (x : H) = inner ℂ (c : H) (S.adjoint x) := by
  have h := adjoint_pairing_closure_right hDense hSymm x c
  calc
    inner ℂ (S.closure c) (x : H) =
        star (inner ℂ (x : H) (S.closure c)) :=
      (inner_conj_symm _ _).symm
    _ = star (inner ℂ (S.adjoint x) (c : H)) :=
      congrArg (starRingEnd ℂ) h.symm
    _ = inner ℂ (c : H) (S.adjoint x) := inner_conj_symm _ _

theorem adjointBoundaryPairing_closure_right {S : H →ₗ.[ℂ] H}
    (hDense : Dense (S.domain : Set H)) (hSymm : S.IsFormalAdjoint S)
    (x : S.adjoint.domain) (c : S.closure.domain) :
    adjointBoundaryPairing S x
      ⟨(c : H), (closure_le_adjoint hDense hSymm).1 c.property⟩ = 0 := by
  rw [adjointBoundaryPairing]
  have hcapp := (closure_le_adjoint hDense hSymm).2
    (show (c : H) =
      (⟨(c : H), (closure_le_adjoint hDense hSymm).1 c.property⟩ :
        S.adjoint.domain) from rfl)
  rw [← hcapp, adjoint_pairing_closure_right hDense hSymm, sub_self]

theorem adjointBoundaryPairing_closure_left {S : H →ₗ.[ℂ] H}
    (hDense : Dense (S.domain : Set H)) (hSymm : S.IsFormalAdjoint S)
    (c : S.closure.domain) (x : S.adjoint.domain) :
    adjointBoundaryPairing S
      ⟨(c : H), (closure_le_adjoint hDense hSymm).1 c.property⟩ x = 0 := by
  rw [adjointBoundaryPairing]
  have hcapp := (closure_le_adjoint hDense hSymm).2
    (show (c : H) =
      (⟨(c : H), (closure_le_adjoint hDense hSymm).1 c.property⟩ :
        S.adjoint.domain) from rfl)
  rw [← hcapp, adjoint_pairing_closure_left hDense hSymm, sub_self]

theorem coefficient_relation_of_boundary_zero {S : H →ₗ.[ℂ] H}
    {p m : S.adjoint.domain} {u alpha beta : ℂ}
    (hp : S.adjoint p = I • (p : H))
    (hm : S.adjoint m = (-I) • (m : H))
    (hp0 : (p : H) ≠ 0) (hnorm : ‖(p : H)‖ = ‖(m : H)‖)
    (hu : ‖u‖ = 1)
    (hboundary : adjointBoundaryPairing S
      (alpha • p + beta • m) (p + u • m) = 0) :
    beta = u * alpha := by
  have hinner : inner ℂ (p : H) (p : H) ≠ 0 := inner_self_ne_zero.mpr hp0
  have hunit : star u * u = 1 := by
    change (starRingEnd ℂ) u * u = 1
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hu]
    norm_num
  have hunit' : u * star u = 1 := by rw [mul_comm, hunit]
  change
    inner ℂ (S.adjoint (alpha • p + beta • m))
        ((p : H) + u • (m : H)) -
      inner ℂ (alpha • (p : H) + beta • (m : H))
        (S.adjoint (p + u • m)) = 0 at hboundary
  rw [map_add, map_smul, map_smul, hp, hm, map_add, map_smul, hp, hm,
    inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    inner_add_left, inner_add_right, inner_smul_left, inner_smul_right] at hboundary
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right] at hboundary
  have hstarI : star (I : ℂ) = -I := by simp
  simp only [starRingEnd_apply, star_neg, hstarI] at hboundary
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, ← hnorm] at hboundary
  have hscalar : u * star beta = star alpha := by
    have hnorm0 : ((‖(p : H)‖ : ℝ) : ℂ) ^ 2 ≠ 0 := by
      rw [ne_eq, sq_eq_zero_iff, Complex.ofReal_eq_zero, norm_eq_zero]
      exact hp0
    apply (mul_left_cancel₀ (mul_ne_zero (by exact Complex.I_ne_zero)
      (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hnorm0)))
    linear_combination hboundary
  have hstar : star u * beta = alpha := by
    have hs := congrArg (starRingEnd ℂ) hscalar
    simpa only [starRingEnd_apply, star_mul, star_star, mul_comm] using hs
  calc
    beta = (u * star u) * beta := by rw [hunit']; simp
    _ = u * (star u * beta) := by ring
    _ = u * alpha := by rw [hstar]

theorem adjointBoundaryPairing_add_left (S : H →ₗ.[ℂ] H)
    (x y z : S.adjoint.domain) :
    adjointBoundaryPairing S (x + y) z =
      adjointBoundaryPairing S x z + adjointBoundaryPairing S y z := by
  change inner ℂ (S.adjoint (x + y)) (z : H) -
      inner ℂ ((x : H) + (y : H)) (S.adjoint z) = _
  rw [map_add]
  simp only [inner_add_left]
  simp only [adjointBoundaryPairing]
  ring

theorem adjointBoundaryPairing_smul_left (S : H →ₗ.[ℂ] H)
    (q : ℂ) (x y : S.adjoint.domain) :
    adjointBoundaryPairing S (q • x) y =
      star q * adjointBoundaryPairing S x y := by
  change inner ℂ (S.adjoint (q • x)) (y : H) -
      inner ℂ (q • (x : H)) (S.adjoint y) = _
  rw [map_smul]
  simp only [inner_smul_left, starRingEnd_apply]
  simp only [adjointBoundaryPairing]
  ring

theorem adjointBoundaryPairing_add_right (S : H →ₗ.[ℂ] H)
    (x y z : S.adjoint.domain) :
    adjointBoundaryPairing S x (y + z) =
      adjointBoundaryPairing S x y + adjointBoundaryPairing S x z := by
  change inner ℂ (S.adjoint x) ((y : H) + (z : H)) -
      inner ℂ (x : H) (S.adjoint (y + z)) = _
  rw [map_add]
  simp only [inner_add_right]
  simp only [adjointBoundaryPairing]
  ring

theorem adjointBoundaryPairing_smul_right (S : H →ₗ.[ℂ] H)
    (q : ℂ) (x y : S.adjoint.domain) :
    adjointBoundaryPairing S x (q • y) =
      q * adjointBoundaryPairing S x y := by
  change inner ℂ (S.adjoint x) (q • (y : H)) -
      inner ℂ (x : H) (S.adjoint (q • y)) = _
  rw [map_smul]
  simp only [inner_smul_right]
  simp only [adjointBoundaryPairing]
  ring

/-- Boundary-vanishing criterion for membership in a self-adjoint deficiency extension.

This is the maximality step needed by characteristic-function realizations: an adjoint-domain
vector belongs to the extension when its Green boundary pairing with the chosen boundary
generator vanishes. -/
theorem mem_deficiencyExtensionDomain_of_boundary_zero {S : H →ₗ.[ℂ] H}
    (hDense : Dense (S.domain : Set H)) (hSymm : S.IsFormalAdjoint S)
    (p m : S.adjoint.domain) (u : ℂ)
    (hSelf : IsSelfAdjoint (deficiencyExtension hDense hSymm p m u))
    (x : S.adjoint.domain)
    (hboundary : adjointBoundaryPairing S x (p + u • m) = 0) :
    (x : H) ∈ (deficiencyExtension hDense hSymm p m u).domain := by
  let A := deficiencyExtension hDense hSymm p m u
  let w : S.adjoint.domain := p + u • m
  have hxAdj : (x : H) ∈ A.adjoint.domain := by
    apply mem_adjoint_domain_of_exists
    refine ⟨S.adjoint x, ?_⟩
    intro y
    obtain ⟨c, q, hy⟩ := exists_closure_add_smul_boundary p m u y.property
    let cAdj : S.adjoint.domain :=
      ⟨(c : H), (closure_le_adjoint hDense hSymm).1 c.property⟩
    let yAdj : S.adjoint.domain :=
      ⟨(y : H), deficiencyExtensionDomain_le_adjoint hDense hSymm p m u y.property⟩
    have hyAdj : yAdj = cAdj + q • w := by
      apply Subtype.ext
      exact hy
    have hxc : adjointBoundaryPairing S x cAdj = 0 :=
      adjointBoundaryPairing_closure_right hDense hSymm x c
    have hxy : adjointBoundaryPairing S x yAdj = 0 := by
      rw [hyAdj, adjointBoundaryPairing_add_right,
        adjointBoundaryPairing_smul_right, hxc, hboundary]
      ring
    change inner ℂ (S.adjoint x) (y : H) = inner ℂ (x : H) (A y)
    rw [show A y = S.adjoint yAdj from rfl]
    exact sub_eq_zero.mp hxy
  have hEq : A.adjoint = A := isSelfAdjoint_def.mp hSelf
  change (x : H) ∈ A.domain
  rw [← hEq]
  exact hxAdj

theorem adjointBoundaryPairing_boundaryVector {S : H →ₗ.[ℂ] H}
    {p m : S.adjoint.domain} {u : ℂ}
    (hp : S.adjoint p = I • (p : H))
    (hm : S.adjoint m = (-I) • (m : H))
    (hnorm : ‖(p : H)‖ = ‖(m : H)‖) (hu : ‖u‖ = 1) :
    adjointBoundaryPairing S (p + u • m) (p + u • m) = 0 := by
  have hunit : star u * u = 1 := by
    change (starRingEnd ℂ) u * u = 1
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hu]
    norm_num
  change
    inner ℂ (S.adjoint (p + u • m)) ((p : H) + u • (m : H)) -
      inner ℂ ((p : H) + u • (m : H)) (S.adjoint (p + u • m)) = 0
  rw [map_add, map_smul, hp, hm]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]
  have hstarI : star (I : ℂ) = -I := by simp
  simp only [starRingEnd_apply, star_neg, hstarI]
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, ← hnorm]
  ring_nf at hunit ⊢
  rw [hunit]
  ring

theorem deficiencyExtension_isSelfAdjoint {S : H →ₗ.[ℂ] H}
    (hDense : Dense (S.domain : Set H)) (hSymm : S.IsFormalAdjoint S)
    {p m : S.adjoint.domain} {u : ℂ}
    (hp : S.adjoint p = I • (p : H))
    (hm : S.adjoint m = (-I) • (m : H))
    (hp0 : (p : H) ≠ 0) (hnorm : ‖(p : H)‖ = ‖(m : H)‖)
    (hu : ‖u‖ = 1)
    (hspanP : ∀ x : S.adjoint.domain, S.adjoint x = I • (x : H) →
      ∃ alpha : ℂ, (x : H) = alpha • (p : H))
    (hspanM : ∀ x : S.adjoint.domain, S.adjoint x = (-I) • (x : H) →
      ∃ beta : ℂ, (x : H) = beta • (m : H)) :
    IsSelfAdjoint (deficiencyExtension hDense hSymm p m u) := by
  let A := deficiencyExtension hDense hSymm p m u
  have hCA := closure_le_adjoint hDense hSymm
  let w : S.adjoint.domain := p + u • m
  have hwBoundary : adjointBoundaryPairing S w w = 0 :=
    adjointBoundaryPairing_boundaryVector hp hm hnorm hu
  have hSymmA : A.IsFormalAdjoint A := by
    intro x y
    obtain ⟨c, alpha, hx⟩ := exists_closure_add_smul_boundary p m u x.property
    obtain ⟨d, beta, hy⟩ := exists_closure_add_smul_boundary p m u y.property
    let cAdj : S.adjoint.domain := ⟨(c : H), hCA.1 c.property⟩
    let dAdj : S.adjoint.domain := ⟨(d : H), hCA.1 d.property⟩
    let xAdj : S.adjoint.domain :=
      ⟨(x : H), deficiencyExtensionDomain_le_adjoint hDense hSymm p m u x.property⟩
    let yAdj : S.adjoint.domain :=
      ⟨(y : H), deficiencyExtensionDomain_le_adjoint hDense hSymm p m u y.property⟩
    have hxAdj : xAdj = cAdj + alpha • w := by
      apply Subtype.ext
      exact hx
    have hyAdj : yAdj = dAdj + beta • w := by
      apply Subtype.ext
      exact hy
    change inner ℂ (S.adjoint xAdj) (y : H) =
      inner ℂ (x : H) (S.adjoint yAdj)
    suffices hzero : adjointBoundaryPairing S xAdj yAdj = 0 by
      exact sub_eq_zero.mp hzero
    have hcd : adjointBoundaryPairing S cAdj dAdj = 0 :=
      adjointBoundaryPairing_closure_left hDense hSymm c dAdj
    have hcw : adjointBoundaryPairing S cAdj w = 0 :=
      adjointBoundaryPairing_closure_left hDense hSymm c w
    have hwd : adjointBoundaryPairing S w dAdj = 0 :=
      adjointBoundaryPairing_closure_right hDense hSymm w d
    have hcY : adjointBoundaryPairing S cAdj (dAdj + beta • w) = 0 := by
      calc
        adjointBoundaryPairing S cAdj (dAdj + beta • w) =
            adjointBoundaryPairing S cAdj dAdj +
              beta * adjointBoundaryPairing S cAdj w := by
          rw [adjointBoundaryPairing_add_right,
            adjointBoundaryPairing_smul_right]
        _ = 0 := by rw [hcd, hcw]; ring
    have hwY : adjointBoundaryPairing S w (dAdj + beta • w) = 0 := by
      calc
        adjointBoundaryPairing S w (dAdj + beta • w) =
            adjointBoundaryPairing S w dAdj +
              beta * adjointBoundaryPairing S w w := by
          rw [adjointBoundaryPairing_add_right,
            adjointBoundaryPairing_smul_right]
        _ = 0 := by rw [hwd, hwBoundary]; ring
    calc
      adjointBoundaryPairing S xAdj yAdj =
          adjointBoundaryPairing S (cAdj + alpha • w) (dAdj + beta • w) := by
        rw [hxAdj, hyAdj]
      _ =
          adjointBoundaryPairing S cAdj (dAdj + beta • w) +
            star alpha * adjointBoundaryPairing S w (dAdj + beta • w) := by
        rw [adjointBoundaryPairing_add_left,
          adjointBoundaryPairing_smul_left]
      _ = 0 := by rw [hcY, hwY]; ring
  have hSA := le_deficiencyExtension hDense hSymm p m u
  have hDenseA : Dense (A.domain : Set H) := hDense.mono hSA.1
  rw [isSelfAdjoint_def]
  apply le_antisymm
  · have hAdjFormal := adjoint_isFormalAdjoint hDenseA
    have hAdjS : A.adjoint.IsFormalAdjoint S := by
      intro x y
      let yA : A.domain := ⟨(y : H), hSA.1 y.property⟩
      have hyapp : S y = A yA := hSA.2 rfl
      simpa [hyapp] using hAdjFormal x yA
    have hAdjLeSAdj : A.adjoint ≤ S.adjoint := hAdjS.symm.le_adjoint hDense
    refine ⟨?_, ?_⟩
    · intro y hy
      let yAAdj : A.adjoint.domain := ⟨y, hy⟩
      have hyS : y ∈ S.adjoint.domain := hAdjLeSAdj.1 hy
      let yS : S.adjoint.domain := ⟨y, hyS⟩
      obtain ⟨c, pp, mm, hpp, hmm, hydec⟩ :=
        exists_closure_add_deficiencies hDense hSymm yS
      obtain ⟨alpha, halpha⟩ := hspanP pp hpp
      obtain ⟨beta, hbeta⟩ := hspanM mm hmm
      have hydecomp : (yS : H) = (c : H) +
          (alpha • p + beta • m : S.adjoint.domain) := by
        calc
          (yS : H) = (c : H) + (pp : H) + (mm : H) := hydec
          _ = (c : H) + alpha • (p : H) + beta • (m : H) := by
            rw [halpha, hbeta]
          _ = (c : H) + (alpha • p + beta • m : S.adjoint.domain) := by
            simp only [Submodule.coe_add, Submodule.coe_smul]
            module
      have hwA : deficiencyBoundaryVector p m u ∈ A.domain := by
        change deficiencyBoundaryVector p m u ∈
          S.closure.domain ⊔ ℂ ∙ deficiencyBoundaryVector p m u
        exact Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton _))
      let wA : A.domain := ⟨deficiencyBoundaryVector p m u, hwA⟩
      have hformal := adjoint_isFormalAdjoint hDenseA yAAdj wA
      have hyapp : A.adjoint yAAdj = S.adjoint yS := hAdjLeSAdj.2 rfl
      have hwapp : A wA = S.adjoint w := by
        change S.adjoint
          ⟨(deficiencyBoundaryVector p m u),
            deficiencyExtensionDomain_le_adjoint hDense hSymm p m u hwA⟩ =
          S.adjoint w
        apply congrArg S.adjoint
        rfl
      have hboundaryY : adjointBoundaryPairing S yS w = 0 := by
        rw [adjointBoundaryPairing, ← hyapp, ← hwapp]
        exact sub_eq_zero.mpr hformal
      have hsmall : adjointBoundaryPairing S
          (alpha • p + beta • m) w = 0 := by
        let cAdj : S.adjoint.domain := ⟨(c : H), hCA.1 c.property⟩
        have hyAdj : yS = cAdj + (alpha • p + beta • m) := by
          apply Subtype.ext
          exact hydecomp
        rw [hyAdj, adjointBoundaryPairing_add_left,
          adjointBoundaryPairing_closure_left hDense hSymm, zero_add] at hboundaryY
        exact hboundaryY
      have hcoeff : beta = u * alpha :=
        coefficient_relation_of_boundary_zero hp hm hp0 hnorm hu hsmall
      change y ∈ S.closure.domain ⊔ ℂ ∙ deficiencyBoundaryVector p m u
      rw [Submodule.mem_sup]
      refine ⟨(c : H), c.property, alpha • deficiencyBoundaryVector p m u,
        ?_, ?_⟩
      · rw [Submodule.mem_span_singleton]
        exact ⟨alpha, rfl⟩
      · change (c : H) + alpha • deficiencyBoundaryVector p m u = y
        calc
          (c : H) + alpha • deficiencyBoundaryVector p m u =
              (c : H) + alpha • (p : H) + (u * alpha) • (m : H) := by
            rw [deficiencyBoundaryVector]
            module
          _ = (yS : H) := by
            rw [← hcoeff]
            calc
              (c : H) + alpha • (p : H) + beta • (m : H) =
                  (c : H) + (alpha • (p : H) + beta • (m : H)) := by module
              _ = (yS : H) := by
                simpa only [Submodule.coe_add, Submodule.coe_smul] using hydecomp.symm
          _ = y := rfl
    · intro x y hxy
      have hxS : (x : H) ∈ S.adjoint.domain := hAdjLeSAdj.1 x.property
      let xS : S.adjoint.domain := ⟨(x : H), hxS⟩
      have hxapp : A.adjoint x = S.adjoint xS := hAdjLeSAdj.2 rfl
      change A.adjoint x = S.adjoint
        ⟨(y : H), deficiencyExtensionDomain_le_adjoint hDense hSymm p m u y.property⟩
      rw [hxapp]
      apply congrArg S.adjoint
      exact Subtype.ext hxy
  · exact hSymmA.le_adjoint hDenseA

end LinearPMap
