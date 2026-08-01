import GaloisForLFunctions.RHTower.SoninPrincipalRelativeCyclicExtension

/-!
# The extended trace is the only gluing of the two normalizations

An operator carrying a principal-relative presentation determines its principal state and its
exact correction, so the glued functional is well defined on the represented operator.  It is also
the only such gluing: any assignment that reads a canonical normal state by its logarithmic weight
and absorbs an exact correction by the ordinary trace agrees with it everywhere on the presented
operators.

This turns directness plus the two restrictions into a characterization of the extended trace.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap SoninPrincipalRelativeOperator

variable {a : ℝ}

/-- The operators carrying a principal-relative presentation. -/
def soninPrincipalRelativeCarrier (a : ℝ) : Set (evenSubspace →L[ℂ] evenSubspace) :=
  Set.range (toOperator (a := a))

theorem toOperator_mem_soninPrincipalRelativeCarrier (X : SoninPrincipalRelativeOperator a) :
    toOperator X ∈ soninPrincipalRelativeCarrier a := ⟨X, rfl⟩

theorem state_operator_mem_soninPrincipalRelativeCarrier (s : SoninWindowState a) :
    s.operator ∈ soninPrincipalRelativeCarrier a :=
  ⟨ofState s, toOperator_ofState s⟩

/-- Adding an exact correction stays inside the presented operators. -/
theorem add_relative_mem_soninPrincipalRelativeCarrier
    (X : SoninPrincipalRelativeOperator a) {K : evenSubspace →L[ℂ] evenSubspace}
    (hK : IsSoninPrincipalRelativeIdeal K) :
    toOperator X + K ∈ soninPrincipalRelativeCarrier a :=
  ⟨⟨X.state, X.relative + K, X.relative_mem.add hK⟩, by
    show X.state.operator + (X.relative + K) = X.state.operator + X.relative + K
    rw [add_assoc]⟩

/-- **Uniqueness of the gluing, on the ambient algebra.**  A functional that reads canonical normal
states by their logarithmic weight and absorbs exact corrections by the ordinary trace is the
extended trace on every presented operator. -/
theorem eq_extendedTrace_of_normalizations
    (F : (evenSubspace →L[ℂ] evenSubspace) → ℂ)
    (hstate : ∀ s : SoninWindowState a,
      F s.operator = (soninWindowStateCyclicLogTrace s : ℂ))
    (hshift : ∀ (s : SoninWindowState a) (K : evenSubspace →L[ℂ] evenSubspace),
      IsSoninPrincipalRelativeIdeal K → F (s.operator + K) = F s.operator + opTrace K)
    (X : SoninPrincipalRelativeOperator a) :
    F (toOperator X) = extendedTrace X := by
  rw [toOperator, hshift X.state X.relative X.relative_mem, hstate, extendedTrace]

/-- Two gluings of the same two normalizations agree on every presented operator. -/
theorem eq_of_normalizations
    (F G : (evenSubspace →L[ℂ] evenSubspace) → ℂ)
    (hFstate : ∀ s : SoninWindowState a,
      F s.operator = (soninWindowStateCyclicLogTrace s : ℂ))
    (hFshift : ∀ (s : SoninWindowState a) (K : evenSubspace →L[ℂ] evenSubspace),
      IsSoninPrincipalRelativeIdeal K → F (s.operator + K) = F s.operator + opTrace K)
    (hGstate : ∀ s : SoninWindowState a,
      G s.operator = (soninWindowStateCyclicLogTrace s : ℂ))
    (hGshift : ∀ (s : SoninWindowState a) (K : evenSubspace →L[ℂ] evenSubspace),
      IsSoninPrincipalRelativeIdeal K → G (s.operator + K) = G s.operator + opTrace K)
    (X : SoninPrincipalRelativeOperator a) :
    F (toOperator X) = G (toOperator X) := by
  rw [eq_extendedTrace_of_normalizations F hFstate hFshift X,
    eq_extendedTrace_of_normalizations G hGstate hGshift X]

/-- The extended trace read off any presentation of the operator. -/
def soninExtendedTraceOn (T : soninPrincipalRelativeCarrier a) : ℂ :=
  extendedTrace (Classical.choose T.2)

theorem soninExtendedTraceOn_eq (ha : 0 < a) (T : soninPrincipalRelativeCarrier a)
    (X : SoninPrincipalRelativeOperator a)
    (hX : toOperator X = (T : evenSubspace →L[ℂ] evenSubspace)) :
    soninExtendedTraceOn T = extendedTrace X :=
  extendedTrace_eq_of_toOperator_eq ha ((Classical.choose_spec T.2).trans hX.symm)

theorem soninExtendedTraceOn_state (ha : 0 < a) (s : SoninWindowState a) :
    soninExtendedTraceOn ⟨s.operator, state_operator_mem_soninPrincipalRelativeCarrier s⟩ =
      (soninWindowStateCyclicLogTrace s : ℂ) := by
  rw [soninExtendedTraceOn_eq ha _ (ofState s) (toOperator_ofState s), extendedTrace_ofState]

theorem soninExtendedTraceOn_add_relative (ha : 0 < a)
    (X : SoninPrincipalRelativeOperator a) {K : evenSubspace →L[ℂ] evenSubspace}
    (hK : IsSoninPrincipalRelativeIdeal K) :
    soninExtendedTraceOn
        ⟨toOperator X + K, add_relative_mem_soninPrincipalRelativeCarrier X hK⟩ =
      soninExtendedTraceOn ⟨toOperator X, toOperator_mem_soninPrincipalRelativeCarrier X⟩ +
        opTrace K := by
  have hsum : toOperator (⟨X.state, X.relative + K, X.relative_mem.add hK⟩ :
      SoninPrincipalRelativeOperator a) = toOperator X + K := by
    show X.state.operator + (X.relative + K) = X.state.operator + X.relative + K
    rw [add_assoc]
  rw [soninExtendedTraceOn_eq ha _ ⟨X.state, X.relative + K, X.relative_mem.add hK⟩ hsum,
    soninExtendedTraceOn_eq ha _ X rfl, extendedTrace, extendedTrace,
    opTrace_add_of_memSchattenClass_one X.relative_mem.memSchattenClass_one
      hK.memSchattenClass_one]
  ring

/-- **The glued functional exists and is unique.**  On the presented operators there is exactly one
assignment reading canonical normal states by their logarithmic weight and absorbing exact
corrections by the ordinary trace. -/
theorem existsUnique_soninExtendedTraceOn (ha : 0 < a) :
    ∃! F : soninPrincipalRelativeCarrier a → ℂ,
      (∀ s : SoninWindowState a,
          F ⟨s.operator, state_operator_mem_soninPrincipalRelativeCarrier s⟩ =
            (soninWindowStateCyclicLogTrace s : ℂ)) ∧
        ∀ (X : SoninPrincipalRelativeOperator a) (K : evenSubspace →L[ℂ] evenSubspace)
          (hK : IsSoninPrincipalRelativeIdeal K),
          F ⟨toOperator X + K, add_relative_mem_soninPrincipalRelativeCarrier X hK⟩ =
            F ⟨toOperator X, toOperator_mem_soninPrincipalRelativeCarrier X⟩ + opTrace K := by
  refine ⟨soninExtendedTraceOn,
    ⟨fun s => soninExtendedTraceOn_state ha s,
      fun X K hK => soninExtendedTraceOn_add_relative ha X hK⟩, ?_⟩
  rintro F ⟨hstate, hshift⟩
  funext T
  obtain ⟨X, hX⟩ := T.2
  have hval : F T = extendedTrace X := by
    have h1 : T = ⟨toOperator (ofState X.state) + X.relative,
        add_relative_mem_soninPrincipalRelativeCarrier (ofState X.state) X.relative_mem⟩ := by
      apply Subtype.ext
      show (T : evenSubspace →L[ℂ] evenSubspace) =
        toOperator (ofState X.state) + X.relative
      rw [toOperator_ofState, ← hX]
      rfl
    have h2 : (⟨toOperator (ofState X.state),
        toOperator_mem_soninPrincipalRelativeCarrier (ofState X.state)⟩ :
          soninPrincipalRelativeCarrier a) =
        ⟨X.state.operator, state_operator_mem_soninPrincipalRelativeCarrier X.state⟩ :=
      Subtype.ext (toOperator_ofState X.state)
    rw [h1, hshift (ofState X.state) X.relative X.relative_mem, h2, hstate X.state,
      extendedTrace]
  rw [hval, soninExtendedTraceOn_eq ha T X hX]

end RHTower
