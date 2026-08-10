import GaloisForLFunctions.HTGeometry.ConstitutiveReporterMeetPromotion

/-!
# Operational semantic transport and arity promotion

A reporter is operationally strengthened precisely when it excludes an intervention that was
previously invisible.  On a finite carrier, every effective cumulative reporter birth strictly
increases attained-image cardinality, so only finitely many births are possible.  Unbounded
genesis therefore needs an escape resource.  One exact escape mechanism is promotion of successive
support arities: its invisible translation tails have split associated grades, and permutation
closure promotes one witnessed support to its full arity orbit.

All declarations are source-independent.  No RH or route premise occurs.
-/

namespace GaloisForLFunctions.HTGeometry

universe u v w

/-- An intervention is invisible to a reporter when it preserves every reported value. -/
def ReporterInvisible {X : Type u} {Y : Type v} (q : X → Y) (a : X → X) : Prop :=
  ∀ x, q (a x) = q x

/-- `r` is determined by `q` when it is constant on every `q`-fibre. -/
def ReporterDeterminedBy {X : Type u} {Y : Type v} {Z : Type w}
    (q : X → Y) (r : X → Z) : Prop :=
  ∀ ⦃x y⦄, q x = q y → r x = r y

/-- **Operational novelty criterion.** A reporter is determined by an older reporter exactly when
every intervention invisible to the old reporter is also invisible to the new one. -/
theorem reporterDeterminedBy_iff_invisible_mono
    {X : Type u} {Y : Type v} {Z : Type w} (q : X → Y) (r : X → Z) :
    ReporterDeterminedBy q r ↔
      ∀ a : X → X, ReporterInvisible q a → ReporterInvisible r a := by
  constructor
  · intro h a ha x
    exact h (ha x)
  · intro h x y hxy
    classical
    let a : X → X := Function.update id x y
    have ha : ReporterInvisible q a := by
      intro z
      by_cases hzx : z = x
      · subst z
        simpa [a] using hxy.symm
      · simp [a, hzx]
    have hr := h a ha x
    simpa [a] using hr.symm

/-- Invisible interventions of a paired reporter are exactly the intersection of the two
invisible-intervention doctrines. -/
theorem reporterInvisible_pairedReporter_iff
    {X : Type u} {Y : Type v} {Z : Type w}
    (q : X → Y) (r : X → Z) (a : X → X) :
    ReporterInvisible (pairedReporter q r) a ↔
      ReporterInvisible q a ∧ ReporterInvisible r a := by
  constructor
  · intro h
    exact ⟨fun x => congrArg Prod.fst (h x), fun x => congrArg Prod.snd (h x)⟩
  · rintro ⟨hq, hr⟩ x
    exact Prod.ext (hq x) (hr x)

/-- Adjoining `r` strictly contracts the old invisible doctrine exactly when `r` is not determined
by `q`.  The witness is an explicit old-invisible intervention. -/
theorem pairedReporter_strict_contraction_iff
    {X : Type u} {Y : Type v} {Z : Type w}
    (q : X → Y) (r : X → Z) :
    (∃ a : X → X,
      ReporterInvisible q a ∧ ¬ ReporterInvisible (pairedReporter q r) a) ↔
      ¬ ReporterDeterminedBy q r := by
  rw [reporterDeterminedBy_iff_invisible_mono]
  constructor
  · rintro ⟨a, hq, hpair⟩ hall
    apply hpair
    exact reporterInvisible_pairedReporter_iff q r a |>.2 ⟨hq, hall a hq⟩
  · intro h
    push Not at h
    obtain ⟨a, hq, hr⟩ := h
    refine ⟨a, hq, ?_⟩
    intro hpair
    exact hr ((reporterInvisible_pairedReporter_iff q r a).1 hpair).2

/-- Attained-image type of a reporter. -/
abbrev ReporterRange {X : Type u} {Y : Type v} (q : X → Y) :=
  {y : Y // y ∈ Set.range q}

/-- Canonical attained value. -/
def reporterRangeValue {X : Type u} {Y : Type v} (q : X → Y) (x : X) :
    ReporterRange q :=
  ⟨q x, ⟨x, rfl⟩⟩

/-- Map from a finer attained image back to a coarser attained image. -/
noncomputable def finerReporterToCoarse
    {X : Type u} {Y : Type v} {Z : Type w} (q : X → Y) (r : X → Z) :
    ReporterRange r → ReporterRange q := fun z =>
  ⟨q (Classical.choose z.2), ⟨Classical.choose z.2, rfl⟩⟩

theorem finerReporterToCoarse_apply
    {X : Type u} {Y : Type v} {Z : Type w}
    (q : X → Y) (r : X → Z)
    (h : ∀ ⦃x y⦄, r x = r y → q x = q y) (x : X) :
    finerReporterToCoarse q r (reporterRangeValue r x) = reporterRangeValue q x := by
  apply SetCoe.ext
  exact h (Classical.choose_spec (show r x ∈ Set.range r from ⟨x, rfl⟩))

/-- Every strict fibre refinement strictly increases attained-image cardinality. -/
theorem reporterRange_card_lt_of_strict_refinement
    {X : Type u} {Y : Type v} {Z : Type w} [Fintype X]
    (q : X → Y) (r : X → Z)
    (href : ∀ ⦃x y⦄, r x = r y → q x = q y)
    (hsplit : ∃ x y, q x = q y ∧ r x ≠ r y) :
    Nat.card (ReporterRange q) < Nat.card (ReporterRange r) := by
  classical
  letI : Fintype (ReporterRange q) := Fintype.ofFinite _
  letI : Fintype (ReporterRange r) := Fintype.ofFinite _
  let f := finerReporterToCoarse q r
  simpa only [Nat.card_eq_fintype_card] using
    (Fintype.card_lt_of_surjective_not_injective f (by
      rintro ⟨_, x, rfl⟩
      exact ⟨reporterRangeValue r x, finerReporterToCoarse_apply q r href x⟩) (by
      rintro hinj
      obtain ⟨x, y, hq, hr⟩ := hsplit
      have heq : f (reporterRangeValue r x) = f (reporterRangeValue r y) := by
        change finerReporterToCoarse q r (reporterRangeValue r x) =
          finerReporterToCoarse q r (reporterRangeValue r y)
        calc
          finerReporterToCoarse q r (reporterRangeValue r x) = reporterRangeValue q x :=
            finerReporterToCoarse_apply q r href x
          _ = reporterRangeValue q y := SetCoe.ext hq
          _ = finerReporterToCoarse q r (reporterRangeValue r y) :=
            (finerReporterToCoarse_apply q r href y).symm
      have hval := congrArg Subtype.val (hinj heq)
      exact hr hval))

/-- An attained reporter image has cardinality at most the finite source carrier. -/
theorem reporterRange_card_le_domain
    {X : Type u} {Y : Type v} [Fintype X] (q : X → Y) :
    Nat.card (ReporterRange q) ≤ Fintype.card X := by
  classical
  letI : Fintype (ReporterRange q) := Fintype.ofFinite _
  simpa only [Nat.card_eq_fintype_card] using Fintype.card_range_le q

/-- **Finite genesis bound.** If each successive cumulative reporter strictly splits an old fibre,
the initial number of attained values plus the history length cannot exceed source cardinality. -/
theorem finite_reporter_genesis_bound
    {X : Type u} [Fintype X] {Y : ℕ → Type v} {m : ℕ}
    (Q : ∀ j, X → Y j)
    (href : ∀ j < m, ∀ ⦃x y⦄,
      Q (j + 1) x = Q (j + 1) y → Q j x = Q j y)
    (hsplit : ∀ j < m, ∃ x y,
      Q j x = Q j y ∧ Q (j + 1) x ≠ Q (j + 1) y) :
    Nat.card (ReporterRange (Q 0)) + m ≤ Fintype.card X := by
  have hstep : ∀ j < m,
      Nat.card (ReporterRange (Q j)) < Nat.card (ReporterRange (Q (j + 1))) := by
    intro j hj
    exact reporterRange_card_lt_of_strict_refinement (Q j) (Q (j + 1))
      (href j hj) (hsplit j hj)
  have hgrow : ∀ j ≤ m,
      Nat.card (ReporterRange (Q 0)) + j ≤ Nat.card (ReporterRange (Q j)) := by
    intro j hj
    induction j with
    | zero => simp
    | succ j ih =>
        have hjm : j < m := Nat.lt_of_succ_le hj
        have hprev := ih (Nat.le_of_lt hjm)
        have hnext := hstep j hjm
        omega
  exact (hgrow m le_rfl).trans (reporterRange_card_le_domain (Q m))

/-- Sharp cumulative reporter: isolate the first `k` points, leaving one residual fibre. -/
def sharpReporter (d k : ℕ) (x : Fin d) : ℕ :=
  min x.val k

theorem sharpReporter_zero (d : ℕ) (x : Fin d) : sharpReporter d 0 x = 0 := by
  simp [sharpReporter]

theorem sharpReporter_refines {d k : ℕ} :
    ∀ ⦃x y : Fin d⦄,
      sharpReporter d (k + 1) x = sharpReporter d (k + 1) y →
      sharpReporter d k x = sharpReporter d k y := by
  intro x y hxy
  calc
    sharpReporter d k x = min (sharpReporter d (k + 1) x) k := by
      simp only [sharpReporter]
      omega
    _ = min (sharpReporter d (k + 1) y) k := congrArg (fun z => min z k) hxy
    _ = sharpReporter d k y := by
      simp only [sharpReporter]
      omega

theorem sharpReporter_splits {d k : ℕ} (hk : k + 1 < d) :
    ∃ x y : Fin d,
      sharpReporter d k x = sharpReporter d k y ∧
      sharpReporter d (k + 1) x ≠ sharpReporter d (k + 1) y := by
  let x : Fin d := ⟨k, Nat.lt_trans (Nat.lt_succ_self k) hk⟩
  let y : Fin d := ⟨k + 1, hk⟩
  refine ⟨x, y, ?_, ?_⟩
  · simp [sharpReporter, x, y]
  · simp [sharpReporter, x, y]

/-- The constant-reporter bound `d - 1` is attained on every nonempty `Fin d`. -/
theorem sharp_finite_reporter_genesis {d : ℕ} (hd : 0 < d) :
    ∃ Q : ℕ → Fin d → ℕ,
      (∀ x, Q 0 x = 0) ∧
      (∀ k < d - 1, ∀ ⦃x y⦄,
        Q (k + 1) x = Q (k + 1) y → Q k x = Q k y) ∧
      (∀ k < d - 1, ∃ x y,
        Q k x = Q k y ∧ Q (k + 1) x ≠ Q (k + 1) y) := by
  refine ⟨sharpReporter d, sharpReporter_zero d, ?_, ?_⟩
  · intro k _
    exact sharpReporter_refines
  · intro k hk
    apply sharpReporter_splits
    omega

/-- The sharp `|X| - 1` history transported from `Fin |X|` to every finite nonempty carrier. -/
theorem sharp_finite_reporter_genesis_on_type
    (X : Type u) [Fintype X] [Nonempty X] :
    ∃ Q : ℕ → X → ℕ,
      (∀ x, Q 0 x = 0) ∧
      (∀ k < Fintype.card X - 1, ∀ ⦃x y⦄,
        Q (k + 1) x = Q (k + 1) y → Q k x = Q k y) ∧
      (∀ k < Fintype.card X - 1, ∃ x y,
        Q k x = Q k y ∧ Q (k + 1) x ≠ Q (k + 1) y) := by
  let e := Fintype.equivFin X
  let Q : ℕ → X → ℕ := fun k x => sharpReporter (Fintype.card X) k (e x)
  refine ⟨Q, ?_, ?_, ?_⟩
  · intro x
    exact sharpReporter_zero (Fintype.card X) (e x)
  · intro k _ x y hxy
    exact sharpReporter_refines hxy
  · intro k hk
    have hkd : k + 1 < Fintype.card X := by omega
    obtain ⟨x, y, hsame, hdiff⟩ := sharpReporter_splits hkd
    refine ⟨e.symm x, e.symm y, ?_, ?_⟩
    · simpa [Q] using hsame
    · simpa [Q] using hdiff

/-- Invisible translation tail after observing all supports of size at most `m`. -/
def ArityTail {I : Type u} {A : Type v} [AddCommGroup A]
    (m : ℕ) (h : Finset I → A) : Prop :=
  ∀ S, S.card ≤ m → h S = 0

/-- Supports of one exact arity. -/
abbrev ExactAritySupport (I : Type u) (k : ℕ) :=
  {S : Finset I // S.card = k}

/-- Restriction to one support grade. -/
def arityGradeRestrict {I : Type u} {A : Type v} [AddCommGroup A]
    (k : ℕ) (h : Finset I → A) : ExactAritySupport I k → A :=
  fun S => h S.1

/-- Zero extension from one exact support grade. -/
def arityGradeZeroExtend {I : Type u} {A : Type v} [AddCommGroup A]
    (k : ℕ) (g : ExactAritySupport I k → A) : Finset I → A :=
  fun S => if hS : S.card = k then g ⟨S, hS⟩ else 0

/-- Zero extension is a canonical section of grade restriction. -/
theorem arityGradeRestrict_zeroExtend
    {I : Type u} {A : Type v} [AddCommGroup A]
    (k : ℕ) (g : ExactAritySupport I k → A) :
    arityGradeRestrict k (arityGradeZeroExtend k g) = g := by
  funext S
  simp [arityGradeRestrict, arityGradeZeroExtend, S.property]

/-- The next-grade zero extension belongs to the preceding invisible tail. -/
theorem arityGradeZeroExtend_mem_tail
    {I : Type u} {A : Type v} [AddCommGroup A]
    (m : ℕ) (g : ExactAritySupport I (m + 1) → A) :
    ArityTail m (arityGradeZeroExtend (m + 1) g) := by
  intro S hS
  simp only [arityGradeZeroExtend]
  split
  · omega
  · rfl

/-- Kernel of next-grade restriction is exactly the next invisible tail. -/
theorem arityGrade_kernel_iff
    {I : Type u} {A : Type v} [AddCommGroup A]
    (m : ℕ) (h : Finset I → A) (hh : ArityTail m h) :
    arityGradeRestrict (m + 1) h = 0 ↔ ArityTail (m + 1) h := by
  constructor
  · intro hr S hS
    by_cases hle : S.card ≤ m
    · exact hh S hle
    · have hcard : S.card = m + 1 := by omega
      have hs := congrFun hr ⟨S, hcard⟩
      simpa [arityGradeRestrict] using hs
  · intro ht
    funext S
    exact ht S.1 (by omega)

/-- Equality of reporters up to one arity horizon. -/
def HorizonEqual {I : Type u} {A : Type v} [AddCommGroup A]
    (m : ℕ) (f g : Finset I → A) : Prop :=
  ∀ S, S.card ≤ m → f S = g S

/-- Translation by one support coefficient system. -/
def supportTranslate {I : Type u} {A : Type v} [AddCommGroup A]
    (h f : Finset I → A) : Finset I → A :=
  fun S => f S + h S

/-- Translation is invisible at horizon `m` exactly when its coefficient belongs to `K_m`. -/
theorem supportTranslate_invisible_iff
    {I : Type u} {A : Type v} [AddCommGroup A]
    (m : ℕ) (h : Finset I → A) :
    (∀ f, HorizonEqual m (supportTranslate h f) f) ↔ ArityTail m h := by
  constructor
  · intro hinv S hS
    have hz := hinv 0 S hS
    simpa [supportTranslate] using hz
  · intro ht f S hS
    simp [supportTranslate, ht S hS]

/-- Every element of `K_m \ K_(m+1)` has a detected next-grade coordinate. -/
theorem next_arity_detected
    {I : Type u} {A : Type v} [AddCommGroup A]
    (m : ℕ) (h : Finset I → A)
    (hm : ArityTail m h) (hnext : ¬ ArityTail (m + 1) h) :
    ∃ S : ExactAritySupport I (m + 1), h S.1 ≠ 0 := by
  simp only [ArityTail, not_forall] at hnext
  obtain ⟨S, hS⟩ := hnext
  push Not at hS
  refine ⟨⟨S, ?_⟩, hS.2⟩
  by_contra hcard
  have hupper := hS.1
  have : S.card ≤ m := by omega
  exact hS.2 (hm S this)

/-- Equivalence of equal-cardinality supports. -/
noncomputable def finsetOrbitEquiv
    {I : Type u} [Fintype I] [DecidableEq I]
    (S T : Finset I) (hcard : S.card = T.card) : S ≃ T :=
  S.equivFin.trans ((finCongr hcard).trans T.equivFin.symm)

/-- Ambient permutation extending an equivalence of equal-cardinality supports. -/
noncomputable def finsetOrbitPerm
    {I : Type u} [Fintype I] [DecidableEq I]
    (S T : Finset I) (hcard : S.card = T.card) : Equiv.Perm I :=
  Equiv.extendSubtype (finsetOrbitEquiv S T hcard)

theorem finsetOrbitPerm_image
    {I : Type u} [Fintype I] [DecidableEq I]
    (S T : Finset I) (hcard : S.card = T.card) :
    S.image (finsetOrbitPerm S T hcard) = T := by
  classical
  ext y
  constructor
  · intro hy
    simp only [Finset.mem_image] at hy
    obtain ⟨x, hx, hxy⟩ := hy
    subst y
    rw [finsetOrbitPerm, Equiv.extendSubtype_apply_of_mem _ x hx]
    exact (finsetOrbitEquiv S T hcard ⟨x, hx⟩).property
  · intro hy
    let e : S ≃ T := finsetOrbitEquiv S T hcard
    let xS : S := e.symm ⟨y, hy⟩
    have hx : (xS : I) ∈ S := xS.property
    refine Finset.mem_image.mpr ⟨(xS : I), hx, ?_⟩
    rw [finsetOrbitPerm, Equiv.extendSubtype_apply_of_mem _ (xS : I) hx]
    exact congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩)

/-- A support-reporter doctrine is closed under every permutation of its source labels. -/
def SupportReporterDoctrine
    {I : Type u} [Fintype I] [DecidableEq I] (D : Set (Finset I)) : Prop :=
  ∀ (e : Equiv.Perm I) (S : Finset I), S ∈ D → S.image e ∈ D

/-- **Orbit-forced grade promotion.** One reported support in a permutation-closed doctrine forces
every support of the same arity. -/
theorem symmetry_closed_support_promotes_grade
    {I : Type u} [Fintype I] [DecidableEq I]
    (D : Set (Finset I)) (hD : SupportReporterDoctrine D)
    {S : Finset I} (hS : S ∈ D) :
    ∀ T : Finset I, T.card = S.card → T ∈ D := by
  intro T hcard
  have himage := hD (finsetOrbitPerm S T hcard.symm) S hS
  rwa [finsetOrbitPerm_image] at himage

end GaloisForLFunctions.HTGeometry
