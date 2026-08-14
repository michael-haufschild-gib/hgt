import GaloisForLFunctions.RHTower.LocalCircuitTraceCapacity

/-!
# The trace monoid of a local circuit alphabet

Words in a local gate alphabet are identified when adjacent independent letters are exchanged.
The exchange relation is a congruence for concatenation, so the quotient is a monoid: the trace
monoid of the alphabet.  Length descends to it, and the pair-projection reconstruction makes it
left and right cancellative.  Cancellativity turns every left-prefix cylinder into a translate of
the whole monoid.

Grading by length identifies the trace monoid with the disjoint union of the fixed-length trace
classes, so every length-graded count transfers to the monoid.
-/

namespace GaloisForLFunctions.RHTower

section TraceMonoid

variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
theorem independentSwap_append_right {independent : α → α → Prop} {u u' : List α}
    (h : IndependentSwap independent u u') (v : List α) :
    IndependentSwap independent (u ++ v) (u' ++ v) := by
  cases h with
  | swap l r a b hab =>
      have h1 : (l ++ a :: b :: r) ++ v = l ++ a :: b :: (r ++ v) := by simp
      have h2 : (l ++ b :: a :: r) ++ v = l ++ b :: a :: (r ++ v) := by simp
      rw [h1, h2]
      exact IndependentSwap.swap l (r ++ v) a b hab

omit [DecidableEq α] in
theorem independentSwap_append_left {independent : α → α → Prop} (u : List α) {v v' : List α}
    (h : IndependentSwap independent v v') :
    IndependentSwap independent (u ++ v) (u ++ v') := by
  cases h with
  | swap l r a b hab =>
      have h1 : u ++ (l ++ a :: b :: r) = (u ++ l) ++ a :: b :: r := by simp
      have h2 : u ++ (l ++ b :: a :: r) = (u ++ l) ++ b :: a :: r := by simp
      rw [h1, h2]
      exact IndependentSwap.swap (u ++ l) r a b hab

omit [DecidableEq α] in
theorem traceEq_append_right {independent : α → α → Prop} {u u' : List α}
    (h : TraceEq independent u u') (v : List α) :
    TraceEq independent (u ++ v) (u' ++ v) := by
  induction h with
  | rel x y hxy => exact Relation.EqvGen.rel _ _ (independentSwap_append_right hxy v)
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ h₁ h₂ => exact Relation.EqvGen.trans _ _ _ h₁ h₂

omit [DecidableEq α] in
theorem traceEq_append_left {independent : α → α → Prop} (u : List α) {v v' : List α}
    (h : TraceEq independent v v') :
    TraceEq independent (u ++ v) (u ++ v') := by
  induction h with
  | rel x y hxy => exact Relation.EqvGen.rel _ _ (independentSwap_append_left u hxy)
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ h₁ h₂ => exact Relation.EqvGen.trans _ _ _ h₁ h₂

omit [DecidableEq α] in
theorem traceEq_append {independent : α → α → Prop} {u u' v v' : List α}
    (hu : TraceEq independent u u') (hv : TraceEq independent v v') :
    TraceEq independent (u ++ v) (u' ++ v') :=
  Relation.EqvGen.trans _ _ _ (traceEq_append_right hu v) (traceEq_append_left u' hv)

/-- Trace equivalence of words as a setoid. -/
def traceSetoid (independent : α → α → Prop) : Setoid (List α) where
  r := TraceEq independent
  iseqv := Relation.EqvGen.is_equivalence _

/-- The trace monoid of a local circuit alphabet. -/
def Trace (independent : α → α → Prop) : Type _ := Quotient (traceSetoid independent)

instance (independent : α → α → Prop) : Monoid (Trace independent) where
  mul := Quotient.map₂ (· ++ ·) fun _ _ hu _ _ hv => traceEq_append hu hv
  one := Quotient.mk (traceSetoid independent) []
  mul_assoc := by
    refine Quotient.ind fun u => Quotient.ind fun v => Quotient.ind fun w => ?_
    refine Quotient.sound ?_
    show TraceEq independent (u ++ v ++ w) (u ++ (v ++ w))
    rw [List.append_assoc]
    exact Relation.EqvGen.refl _
  one_mul := by
    refine Quotient.ind fun u => ?_
    refine Quotient.sound ?_
    show TraceEq independent ([] ++ u) u
    rw [List.nil_append]
    exact Relation.EqvGen.refl _
  mul_one := by
    refine Quotient.ind fun u => ?_
    refine Quotient.sound ?_
    show TraceEq independent (u ++ []) u
    rw [List.append_nil]
    exact Relation.EqvGen.refl _

instance (independent : α → α → Prop) [Countable α] : Countable (Trace independent) :=
  inferInstanceAs (Countable (Quotient (traceSetoid independent)))

/-- The class of a word in the trace monoid. -/
def traceMk (independent : α → α → Prop) (w : List α) : Trace independent :=
  Quotient.mk (traceSetoid independent) w

omit [DecidableEq α] in
theorem traceMk_mul (independent : α → α → Prop) (u v : List α) :
    traceMk independent u * traceMk independent v = traceMk independent (u ++ v) := rfl

omit [DecidableEq α] in
theorem traceMk_surjective (independent : α → α → Prop) :
    Function.Surjective (traceMk independent) :=
  Quotient.mk_surjective

omit [DecidableEq α] in
theorem traceMk_eq_iff (independent : α → α → Prop) {u v : List α} :
    traceMk independent u = traceMk independent v ↔ TraceEq independent u v :=
  Quotient.eq

/-- Length of a trace. -/
def traceLen (independent : α → α → Prop) : Trace independent → ℕ :=
  Quotient.lift List.length fun _ _ h => (traceEq_perm h).length_eq

omit [DecidableEq α] in
@[simp]
theorem traceLen_traceMk (independent : α → α → Prop) (w : List α) :
    traceLen independent (traceMk independent w) = w.length := rfl

omit [DecidableEq α] in
theorem traceLen_mul (independent : α → α → Prop) (u v : Trace independent) :
    traceLen independent (u * v) = traceLen independent u + traceLen independent v := by
  obtain ⟨a, rfl⟩ := traceMk_surjective independent u
  obtain ⟨b, rfl⟩ := traceMk_surjective independent v
  rw [traceMk_mul, traceLen_traceMk, traceLen_traceMk, traceLen_traceMk, List.length_append]

omit [DecidableEq α] in
@[simp]
theorem traceLen_one (independent : α → α → Prop) :
    traceLen independent (1 : Trace independent) = 0 := rfl

/-- **Cancellativity of the trace monoid.**  Pair projections and multiplicities reconstruct a
trace, so a common left factor can be removed. -/
theorem trace_mul_left_cancel {independent : α → α → Prop}
    (hsymm : ∀ x y, independent x y → independent y x) {u v w : Trace independent}
    (h : u * v = u * w) : v = w := by
  obtain ⟨a, rfl⟩ := traceMk_surjective independent u
  obtain ⟨b, rfl⟩ := traceMk_surjective independent v
  obtain ⟨c, rfl⟩ := traceMk_surjective independent w
  rw [traceMk_mul, traceMk_mul, traceMk_eq_iff] at h
  have hEq : TraceEq independent (a ++ b) (a ++ c) := h
  have hperm : b.Perm c := (List.perm_append_left_iff a).mp (traceEq_perm hEq)
  have hproj : ∀ x y, x ≠ y → ¬independent x y →
      pairProjection x y b = pairProjection x y c := by
    intro x y hxy hdep
    have hfull := pairProjection_eq_of_traceEq hsymm hdep hEq
    rw [pairProjection_append, pairProjection_append] at hfull
    exact List.append_cancel_left hfull
  exact (traceMk_eq_iff independent).mpr (traceEq_of_perm_of_pairProjections hsymm hperm hproj)

theorem trace_mul_right_cancel {independent : α → α → Prop}
    (hsymm : ∀ x y, independent x y → independent y x) {u v w : Trace independent}
    (h : v * u = w * u) : v = w := by
  obtain ⟨a, rfl⟩ := traceMk_surjective independent u
  obtain ⟨b, rfl⟩ := traceMk_surjective independent v
  obtain ⟨c, rfl⟩ := traceMk_surjective independent w
  rw [traceMk_mul, traceMk_mul, traceMk_eq_iff] at h
  have hEq : TraceEq independent (b ++ a) (c ++ a) := h
  have hperm : b.Perm c := (List.perm_append_right_iff a).mp (traceEq_perm hEq)
  have hproj : ∀ x y, x ≠ y → ¬independent x y →
      pairProjection x y b = pairProjection x y c := by
    intro x y hxy hdep
    have hfull := pairProjection_eq_of_traceEq hsymm hdep hEq
    rw [pairProjection_append, pairProjection_append] at hfull
    exact List.append_cancel_right hfull
  exact (traceMk_eq_iff independent).mpr (traceEq_of_perm_of_pairProjections hsymm hperm hproj)

/-- The left-prefix order of the trace monoid: `u` is a causal prefix of `T`. -/
def TracePrefix (independent : α → α → Prop) (u T : Trace independent) : Prop :=
  ∃ v, T = u * v

/-- The causal cylinder above a trace. -/
def traceCylinder (independent : α → α → Prop) (u : Trace independent) :
    Set (Trace independent) := {T | TracePrefix independent u T}

omit [DecidableEq α] in
theorem tracePrefix_one (independent : α → α → Prop) (T : Trace independent) :
    TracePrefix independent 1 T := ⟨T, (one_mul T).symm⟩

omit [DecidableEq α] in
theorem tracePrefix_refl (independent : α → α → Prop) (u : Trace independent) :
    TracePrefix independent u u := ⟨1, (mul_one u).symm⟩

omit [DecidableEq α] in
theorem traceCylinder_one (independent : α → α → Prop) :
    traceCylinder independent (1 : Trace independent) = Set.univ :=
  Set.eq_univ_of_forall fun T => tracePrefix_one independent T

/-- Cancellativity makes left translation a bijection onto a causal cylinder. -/
noncomputable def traceCylinderEquiv {independent : α → α → Prop}
    (hsymm : ∀ x y, independent x y → independent y x) (u : Trace independent) :
    Trace independent ≃ traceCylinder independent u where
  toFun v := ⟨u * v, ⟨v, rfl⟩⟩
  invFun T := T.2.choose
  left_inv v :=
    trace_mul_left_cancel hsymm
      (((⟨u * v, (⟨v, rfl⟩ : TracePrefix independent u (u * v))⟩ :
        traceCylinder independent u).2.choose_spec).symm)
  right_inv T := Subtype.ext (T.2.choose_spec).symm

omit [DecidableEq α] in
theorem traceLen_of_mem_traceCylinder {independent : α → α → Prop} {u T : Trace independent}
    (h : T ∈ traceCylinder independent u) :
    traceLen independent u ≤ traceLen independent T := by
  obtain ⟨v, hv⟩ := h
  subst hv
  rw [traceLen_mul]
  exact Nat.le_add_right _ _

/-- Two distinct independent letters both prefixing a trace force their product to prefix it. -/
theorem tracePrefix_mul_of_independent {independent : α → α → Prop}
    (hsymm : ∀ x y, independent x y → independent y x) {a b : α} (hab : a ≠ b)
    {T : Trace independent}
    (ha : TracePrefix independent (traceMk independent [a]) T)
    (hb : TracePrefix independent (traceMk independent [b]) T) :
    TracePrefix independent (traceMk independent [a, b]) T := by
  obtain ⟨v, hv⟩ := ha
  obtain ⟨w, hw⟩ := hb
  obtain ⟨v', rfl⟩ := traceMk_surjective independent v
  obtain ⟨w', rfl⟩ := traceMk_surjective independent w
  rw [traceMk_mul] at hv hw
  simp only [List.singleton_append] at hv hw
  have hEq : TraceEq independent (b :: w') (a :: v') :=
    (traceMk_eq_iff independent).mp (hw.symm.trans hv)
  have hbmem : b ∈ a :: v' := (traceEq_perm hEq).mem_iff.mp (by simp)
  obtain ⟨p, q, hpq, hbp⟩ := exists_first_cons_of_mem hbmem
  have hproj : ∀ c d, c ≠ d → ¬independent c d →
      pairProjection c d (b :: w') = pairProjection c d (p ++ b :: q) := by
    intro c d _ hdep
    rw [← hpq]
    exact pairProjection_eq_of_traceEq hsymm hdep hEq
  have hind : ∀ c ∈ p, independent b c :=
    prefix_independent_of_pairProjections hbp hproj
  have hpne : p ≠ [] := by
    intro hnil
    rw [hnil, List.nil_append] at hpq
    exact hab (List.head_eq_of_cons_eq hpq)
  obtain ⟨c, p₀, rfl⟩ := List.exists_cons_of_ne_nil hpne
  have hac : a = c := List.head_eq_of_cons_eq hpq
  have hv'eq : v' = p₀ ++ b :: q := List.tail_eq_of_cons_eq hpq
  have hind₀ : ∀ e ∈ p₀, independent b e := fun e he => hind e (by simp [he])
  have hmove : TraceEq independent (p₀ ++ b :: q) (b :: (p₀ ++ q)) :=
    traceEq_move_front hind₀ hsymm
  refine ⟨traceMk independent (p₀ ++ q), ?_⟩
  rw [traceMk_mul]
  refine hv.trans ((traceMk_eq_iff independent).mpr ?_)
  rw [hv'eq]
  simpa using traceEq_cons a hmove

/-- Two independent letters have their product as the meet of their causal cylinders. -/
theorem traceCylinder_inter_of_independent {independent : α → α → Prop}
    (hsymm : ∀ x y, independent x y → independent y x) {a b : α} (hab : a ≠ b)
    (hind : independent a b) :
    traceCylinder independent (traceMk independent [a]) ∩
        traceCylinder independent (traceMk independent [b]) =
      traceCylinder independent (traceMk independent [a, b]) := by
  ext T
  constructor
  · rintro ⟨hA, hB⟩
    exact tracePrefix_mul_of_independent hsymm hab hA hB
  · rintro ⟨v, rfl⟩
    have hsplit : traceMk independent [a, b] =
        traceMk independent [a] * traceMk independent [b] := by
      rw [traceMk_mul]; rfl
    have hswap : traceMk independent [a, b] = traceMk independent [b, a] :=
      (traceMk_eq_iff independent).mpr
        (Relation.EqvGen.rel _ _ (IndependentSwap.swap [] [] a b hind))
    have hsplit' : traceMk independent [a, b] =
        traceMk independent [b] * traceMk independent [a] := by
      rw [hswap, traceMk_mul]; rfl
    exact ⟨⟨traceMk independent [b] * v, by rw [hsplit, mul_assoc]⟩,
      ⟨traceMk independent [a] * v, by rw [hsplit', mul_assoc]⟩⟩

end TraceMonoid

section Grading

variable {α : Type*} [DecidableEq α]

/-- A fixed-length trace class as a trace. -/
def fixedTraceToTrace (independent : α → α → Prop) (ℓ : ℕ) :
    FixedTraceClass independent ℓ → Trace independent :=
  Quotient.lift (fun v : List.Vector α ℓ => traceMk independent v.1) fun _ _ h => Quotient.sound h

omit [DecidableEq α] in
theorem traceLen_fixedTraceToTrace (independent : α → α → Prop) (ℓ : ℕ)
    (c : FixedTraceClass independent ℓ) :
    traceLen independent (fixedTraceToTrace independent ℓ c) = ℓ := by
  refine Quotient.inductionOn c fun v => ?_
  simp [fixedTraceToTrace, traceMk]
  exact v.2

omit [DecidableEq α] in
theorem fixedTraceToTrace_injective (independent : α → α → Prop) (ℓ : ℕ) :
    Function.Injective (fixedTraceToTrace independent ℓ) := by
  refine fun c d h => Quotient.inductionOn₂ c d (motive := fun c d =>
    fixedTraceToTrace independent ℓ c = fixedTraceToTrace independent ℓ d → c = d) ?_ h
  intro v w hvw
  have h : traceMk independent v.1 = traceMk independent w.1 := hvw
  exact Quotient.sound ((traceMk_eq_iff independent).mp h)

/-- **Length grading of the trace monoid.**  Traces are exactly the disjoint union of the
fixed-length trace classes. -/
noncomputable def traceGradeEquiv (independent : α → α → Prop) :
    (Σ ℓ : ℕ, FixedTraceClass independent ℓ) ≃ Trace independent := by
  refine Equiv.ofBijective (fun p => fixedTraceToTrace independent p.1 p.2) ⟨?_, ?_⟩
  · rintro ⟨ℓ, c⟩ ⟨m, d⟩ h
    have hlen : ℓ = m := by
      have hc := congrArg (traceLen independent) h
      simpa only [traceLen_fixedTraceToTrace] using hc
    subst hlen
    exact Sigma.ext rfl (heq_of_eq (fixedTraceToTrace_injective independent ℓ h))
  · intro T
    obtain ⟨w, rfl⟩ := traceMk_surjective independent T
    exact ⟨⟨w.length, Quotient.mk _ ⟨w, rfl⟩⟩, rfl⟩

omit [DecidableEq α] in
theorem traceLen_traceGradeEquiv (independent : α → α → Prop)
    (p : Σ ℓ : ℕ, FixedTraceClass independent ℓ) :
    traceLen independent (traceGradeEquiv independent p) = p.1 :=
  traceLen_fixedTraceToTrace independent p.1 p.2

end Grading

end GaloisForLFunctions.RHTower
