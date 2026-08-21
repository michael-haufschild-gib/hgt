import GaloisForLFunctions.RHTower.ConnesGraphDelta

/-!
# The transverse map of a periodic orbit

Appendix III (37)-(42) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

Along a periodic orbit the fixed-point set `W = {(x,t) : F_t x = x}` is one-dimensional and its
transverse space splits as `N_x × ℝ`, `N_x = T_x/ℝv_x`.  The differential of the diagonal map is

  `φ_*(X, λ∂_t) = (1 − (F_t)_*) X − λ v`   (41),

and the symbol of the graph `δ`-section is `|φ_*^{-1}|` (42).  Since `(F_t)_*` fixes `v`, the
operator `1 − (F_t)_*` descends to the transverse space, and `φ_*` is an isomorphism exactly when
`1 − P` is one on `N_x`, `P` the Poincaré return map.  That is Appendix III's transversality in
the form actually used by the trace computation.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem connesFlowLine_le_ker_one_sub {v : V} {A : V →ₗ[ℝ] V} (hA : A v = v) :
    connesFlowLine v ≤ LinearMap.ker ((LinearMap.id : V →ₗ[ℝ] V) - A) := by
  rw [connesFlowLine, Submodule.span_le]
  rintro x hx
  simp only [Set.mem_singleton_iff] at hx
  subst hx
  simp [LinearMap.mem_ker, hA]

/-- The descent of `1 − (F_t)_*` to the transverse space: it kills the flow direction. -/
def connesOneSubDescend {v : V} {A : V →ₗ[ℝ] V} (hA : A v = v) :
    (V ⧸ connesFlowLine v) →ₗ[ℝ] V :=
  Submodule.liftQ (connesFlowLine v) ((LinearMap.id : V →ₗ[ℝ] V) - A)
    (connesFlowLine_le_ker_one_sub hA)

@[simp] theorem connesOneSubDescend_mk {v : V} {A : V →ₗ[ℝ] V} (hA : A v = v) (x : V) :
    connesOneSubDescend hA (Submodule.Quotient.mk x) = x - A x := rfl

/-- **Appendix III (41).**  The differential of the diagonal map on the transverse space of a
periodic orbit. -/
def connesFlowTransverseMap {v : V} {A : V →ₗ[ℝ] V} (hA : A v = v) :
    ((V ⧸ connesFlowLine v) × ℝ) →ₗ[ℝ] V :=
  (connesOneSubDescend hA).comp (LinearMap.fst ℝ _ ℝ)
    - (LinearMap.toSpanSingleton ℝ V v).comp (LinearMap.snd ℝ _ ℝ)

theorem connesFlowTransverseMap_apply {v : V} {A : V →ₗ[ℝ] V} (hA : A v = v)
    (X : V ⧸ connesFlowLine v) (lam : ℝ) :
    connesFlowTransverseMap hA (X, lam) = connesOneSubDescend hA X - lam • v := rfl

theorem connes_quotient_comp_descend {v : V} {A : V →ₗ[ℝ] V} (hA : A v = v)
    (X : V ⧸ connesFlowLine v) :
    Submodule.Quotient.mk (p := connesFlowLine v) (connesOneSubDescend hA X)
      = ((LinearMap.id : (V ⧸ connesFlowLine v) →ₗ[ℝ] (V ⧸ connesFlowLine v))
          - connesReturnMap hA) X := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (connesFlowLine v) X
  simp only [connesOneSubDescend_mk, LinearMap.sub_apply, LinearMap.id_apply,
    connesReturnMap_mk]
  rw [← Submodule.Quotient.mk_sub]

/-- **Appendix III (42), injectivity half.** -/
theorem connesFlowTransverseMap_injective_iff {v : V} (hv : v ≠ 0) {A : V →ₗ[ℝ] V}
    (hA : A v = v) :
    Function.Injective (connesFlowTransverseMap hA)
      ↔ Function.Injective
          (⇑((LinearMap.id : (V ⧸ connesFlowLine v) →ₗ[ℝ] (V ⧸ connesFlowLine v))
              - connesReturnMap hA)) := by
  rw [injective_iff_map_eq_zero (connesFlowTransverseMap hA),
    injective_iff_map_eq_zero
      ((LinearMap.id : (V ⧸ connesFlowLine v) →ₗ[ℝ] (V ⧸ connesFlowLine v))
        - connesReturnMap hA)]
  constructor
  · intro h X hX
    have hq : Submodule.Quotient.mk (p := connesFlowLine v)
        (connesOneSubDescend hA X) = 0 := by
      rw [connes_quotient_comp_descend hA X, hX]
    have hmem : connesOneSubDescend hA X ∈ connesFlowLine v :=
      (Submodule.Quotient.mk_eq_zero _).mp hq
    obtain ⟨lam, hlam⟩ := Submodule.mem_span_singleton.mp hmem
    have hzero : connesFlowTransverseMap hA (X, lam) = 0 := by
      rw [connesFlowTransverseMap_apply, ← hlam, sub_self]
    have := h (X, lam) hzero
    exact congrArg Prod.fst this
  · intro h z hz
    obtain ⟨X, lam⟩ := z
    rw [connesFlowTransverseMap_apply] at hz
    have hmem : connesOneSubDescend hA X = lam • v := by
      rw [sub_eq_zero] at hz
      exact hz
    have hq : ((LinearMap.id : (V ⧸ connesFlowLine v) →ₗ[ℝ] (V ⧸ connesFlowLine v))
        - connesReturnMap hA) X = 0 := by
      rw [← connes_quotient_comp_descend hA X, hmem]
      exact (Submodule.Quotient.mk_eq_zero _).mpr
        (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v))
    have hX0 : X = 0 := h X hq
    have hlam : lam • v = 0 := by
      rw [← hmem, hX0]
      simp
    have hl0 : lam = 0 := by
      rcases smul_eq_zero.mp hlam with h1 | h2
      · exact h1
      · exact absurd h2 hv
    simp [hX0, hl0]

/-- **Appendix III (42), surjectivity half.** -/
theorem connesFlowTransverseMap_surjective_iff {v : V} {A : V →ₗ[ℝ] V} (hA : A v = v) :
    Function.Surjective (connesFlowTransverseMap hA)
      ↔ Function.Surjective
          (⇑((LinearMap.id : (V ⧸ connesFlowLine v) →ₗ[ℝ] (V ⧸ connesFlowLine v))
              - connesReturnMap hA)) := by
  constructor
  · intro h q
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective (connesFlowLine v) q
    obtain ⟨⟨X, lam⟩, hXlam⟩ := h w
    refine ⟨X, ?_⟩
    rw [← connes_quotient_comp_descend hA X]
    rw [connesFlowTransverseMap_apply] at hXlam
    have hlam : connesOneSubDescend hA X = w + lam • v := by
      rw [← hXlam]
      abel
    have hzero : Submodule.Quotient.mk (p := connesFlowLine v) (lam • v) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr
        (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v))
    rw [hlam, Submodule.Quotient.mk_add, hzero, add_zero]
  · intro h w
    obtain ⟨X, hX⟩ := h (Submodule.Quotient.mk w)
    have hmem : connesOneSubDescend hA X - w ∈ connesFlowLine v := by
      refine (Submodule.Quotient.eq _).mp ?_
      rw [connes_quotient_comp_descend hA X, hX]
    obtain ⟨lam, hlam⟩ := Submodule.mem_span_singleton.mp hmem
    refine ⟨(X, lam), ?_⟩
    rw [connesFlowTransverseMap_apply, hlam]
    abel

/-- **Appendix III (42).**  The transverse differential of the diagonal map along a periodic orbit
is an isomorphism exactly when `1 − P` is one on the transverse space. -/
theorem connesFlowTransverseMap_bijective_iff {v : V} (hv : v ≠ 0) {A : V →ₗ[ℝ] V}
    (hA : A v = v) :
    Function.Bijective (connesFlowTransverseMap hA)
      ↔ Function.Bijective
          (⇑((LinearMap.id : (V ⧸ connesFlowLine v) →ₗ[ℝ] (V ⧸ connesFlowLine v))
              - connesReturnMap hA)) := by
  rw [Function.Bijective, Function.Bijective,
    connesFlowTransverseMap_injective_iff hv hA, connesFlowTransverseMap_surjective_iff hA]

end

end GaloisForLFunctions.RHTower
