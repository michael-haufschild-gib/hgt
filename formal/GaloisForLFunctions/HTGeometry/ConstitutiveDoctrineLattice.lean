import GaloisForLFunctions.HTGeometry.ConstitutiveDeterminantTorsion

/-!
# Equivalence-lattice nondistributivity, finite recurrence, and cofinal lift reconstruction

An observer doctrine on a source set is an equivalence relation: the observer retains the quotient
and declares equivalent source states indistinguishable.  This file certifies three facts about
that picture.

* `doctrine_not_distributive` — on a three-element source the doctrine lattice is nondistributive:
  three pairwise-crossing doctrines have pairwise meet the equality relation and pairwise join the
  indiscrete relation, so `α ⊓ (β ⊔ γ) = α` while `(α ⊓ β) ⊔ (α ⊓ γ) = ⊥`.
* `jointObserver_periodic_iff`, `jointObserver_fibre_infinite` — every *finite* family of
  congruence doctrines on `ℤ` sees the translation `n ↦ n + 1` as an exactly periodic history, of
  period the least common multiple, with infinite fibres, so it cannot reconstruct the lift.
* `modDoctrine_iInf_eq_bot` — the cofinal family of all congruence doctrines separates points, so it
  reconstructs the open lifted translation.

The phase doctrine `|z| = |w|` on `ℂˣ` is the same phenomenon in another guise: its quotient is
exactly `ℝ_{>0}` and it turns the winding loop of `ULF-TORS-1` into a constant history while the
logarithmic lift stays open.
-/

namespace GaloisForLFunctions.HTGeometry

section DoctrineLattice

/-- The observer doctrine on a three-element source that separates `k` from the other two states
and identifies those two with each other. -/
def pointDoctrine (k : Fin 3) : Setoid (Fin 3) where
  r a b := (a == k) = (b == k)
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

theorem pointDoctrine_apply (k a b : Fin 3) :
    pointDoctrine k a b ↔ ((a == k) = (b == k)) := Iff.rfl

theorem pointDoctrine_of_ne {k x y : Fin 3} (hx : x ≠ k) (hy : y ≠ k) : pointDoctrine k x y := by
  rw [pointDoctrine_apply, beq_eq_false_iff_ne.mpr hx, beq_eq_false_iff_ne.mpr hy]

/-- Two distinct point doctrines already separate every pair of source states. -/
theorem pointPair_separating : ∀ j k : Fin 3, j ≠ k → ∀ a b : Fin 3,
    ((a == j) = (b == j)) → ((a == k) = (b == k)) → a = b := by decide

/-- **Distinct doctrines meet in the equality relation.** -/
theorem inf_pointDoctrine {j k : Fin 3} (hjk : j ≠ k) :
    pointDoctrine j ⊓ pointDoctrine k = ⊥ := by
  refine Setoid.ext fun a b => ?_
  rw [Setoid.bot_def]
  constructor
  · rintro ⟨h1, h2⟩
    exact pointPair_separating j k hjk a b h1 h2
  · rintro rfl
    exact ⟨rfl, rfl⟩

/-- **Distinct doctrines join to the indiscrete relation.** -/
theorem sup_pointDoctrine {j k : Fin 3} (hjk : j ≠ k) :
    pointDoctrine j ⊔ pointDoctrine k = ⊤ := by
  have hex : ∀ j k : Fin 3, j ≠ k → ∃ l : Fin 3, l ≠ j ∧ l ≠ k := by decide
  obtain ⟨l, hlj, hlk⟩ := hex j k hjk
  refine eq_top_iff.mpr ?_
  rw [Setoid.le_def]
  intro a b _
  have key : ∀ x : Fin 3, (pointDoctrine j ⊔ pointDoctrine k) x l := by
    intro x
    by_cases hxj : x = j
    · have hxk : x ≠ k := by rw [hxj]; exact hjk
      exact Setoid.le_def.mp le_sup_right (pointDoctrine_of_ne hxk hlk)
    · exact Setoid.le_def.mp le_sup_left (pointDoctrine_of_ne hxj hlj)
  exact Setoid.trans' _ (key a) (Setoid.symm' _ (key b))

theorem pointDoctrine_ne_bot (k : Fin 3) : pointDoctrine k ≠ ⊥ := by
  have hex : ∀ k : Fin 3, ∃ a b : Fin 3, a ≠ b ∧ a ≠ k ∧ b ≠ k := by decide
  obtain ⟨a, b, hab, hak, hbk⟩ := hex k
  intro hcon
  have h : pointDoctrine k a b := pointDoctrine_of_ne hak hbk
  rw [hcon, Setoid.bot_def] at h
  exact hab h

/-- **Observer doctrines do not form a distributive geometry.**  On a three-element source the
lattice of equivalence relations fails distributivity at the three point doctrines. -/
theorem doctrine_not_distributive :
    pointDoctrine 2 ⊓ (pointDoctrine 1 ⊔ pointDoctrine 0) ≠
      (pointDoctrine 2 ⊓ pointDoctrine 1) ⊔ (pointDoctrine 2 ⊓ pointDoctrine 0) := by
  rw [sup_pointDoctrine (by decide : (1 : Fin 3) ≠ 0), inf_top_eq,
    inf_pointDoctrine (by decide : (2 : Fin 3) ≠ 1),
    inf_pointDoctrine (by decide : (2 : Fin 3) ≠ 0), sup_idem]
  exact pointDoctrine_ne_bot 2

end DoctrineLattice

section Recurrence

/-- The source history: translation by one. -/
def sourceShift : ℤ → ℤ := fun n => n + 1

/-- The congruence doctrine modulo `m`. -/
def modDoctrine (m : ℕ) : Setoid ℤ := Setoid.ker (fun n : ℤ => (n : ZMod m))

theorem modDoctrine_apply (m : ℕ) (n n' : ℤ) :
    modDoctrine m n n' ↔ (n : ZMod m) = (n' : ZMod m) := Iff.rfl

/-- The induced history on the quotient is translation by one on `ZMod m`. -/
theorem sourceShift_mod (m : ℕ) (n : ℤ) :
    ((sourceShift n : ℤ) : ZMod m) = ((n : ℤ) : ZMod m) + 1 := by
  simp [sourceShift]

theorem shiftMod_iterate (m k : ℕ) (x : ZMod m) :
    (fun y : ZMod m => y + 1)^[k] x = x + (k : ZMod m) := by
  induction k with
  | zero => simp
  | succ p ih =>
    rw [Function.iterate_succ_apply', ih]
    push_cast
    ring

/-- **Every finite doctrine sees closed recurrence, with exact period.**  The induced history on
`ZMod m` closes after exactly `m` steps and not before. -/
theorem induced_history_exact_period (m : ℕ) (_hm : 2 ≤ m) :
    ((fun y : ZMod m => y + 1)^[m] = id) ∧
      ∀ k : ℕ, 0 < k → k < m → (fun y : ZMod m => y + 1)^[k] ≠ id := by
  constructor
  · funext x
    rw [shiftMod_iterate]
    simp
  · intro k hk hkm hcon
    have h0 : (0 : ZMod m) + (k : ZMod m) = 0 := by
      rw [← shiftMod_iterate m k 0, hcon]
      rfl
    rw [zero_add] at h0
    have hdvd : m ∣ k := (ZMod.natCast_eq_zero_iff k m).mp h0
    exact absurd (Nat.le_of_dvd hk hdvd) (by omega)

/-- The joint observer attached to a finite family of congruence doctrines. -/
def jointObserver (F : Finset ℕ) : ℤ → (∀ m : F, ZMod m) := fun n m => (n : ZMod m)

theorem jointObserver_eq_iff (F : Finset ℕ) (hF : ∀ m ∈ F, 2 ≤ m) (n k : ℤ) :
    jointObserver F (n + k) = jointObserver F n ↔ ∀ m ∈ F, (m : ℤ) ∣ k := by
  constructor
  · intro h m hm
    have hne : NeZero m := ⟨by have := hF m hm; omega⟩
    have := congrFun h ⟨m, hm⟩
    simp only [jointObserver, Int.cast_add] at this
    have h1 : ((n : ℤ) : ZMod m) + ((k : ℤ) : ZMod m) = ((n : ℤ) : ZMod m) + 0 := by
      rw [add_zero]; exact this
    have h0 : ((k : ℤ) : ZMod m) = 0 := add_left_cancel h1
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd k m).mp h0
  · intro h
    funext m
    have hne : NeZero (m : ℕ) := ⟨by have := hF m.1 m.2; omega⟩
    have h0 : ((k : ℤ) : ZMod (m : ℕ)) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd k m).mpr (h m.1 m.2)
    simp only [jointObserver, Int.cast_add, h0, add_zero]

theorem natCast_dvd_int (m : ℕ) (k : ℤ) : (m : ℤ) ∣ k ↔ m ∣ k.natAbs := by
  rw [← Int.natAbs_dvd_natAbs]
  simp

/-- **The exact joint period is the least common multiple.** -/
theorem jointObserver_periodic_iff (F : Finset ℕ) (hF : ∀ m ∈ F, 2 ≤ m) (n k : ℤ) :
    jointObserver F (n + k) = jointObserver F n ↔ ((F.lcm id : ℕ) : ℤ) ∣ k := by
  rw [jointObserver_eq_iff F hF n k]
  constructor
  · intro h
    rw [natCast_dvd_int]
    refine (Finset.lcm_dvd_iff (s := F) (f := id) (a := k.natAbs)).mpr ?_
    intro m hm
    exact (natCast_dvd_int m k).mp (h m hm)
  · intro h m hm
    refine dvd_trans ?_ h
    exact Int.natCast_dvd_natCast.mpr (Finset.dvd_lcm hm)

/-- **The finite joint observer has infinite fibres**, so it cannot reconstruct the lift. -/
theorem jointObserver_fibre_infinite (F : Finset ℕ) (hF : ∀ m ∈ F, 2 ≤ m) :
    {n : ℤ | jointObserver F n = jointObserver F 0}.Infinite := by
  have hlcm : (0 : ℕ) < F.lcm id := by
    rcases Nat.eq_zero_or_pos (F.lcm id) with h | h
    · exfalso
      rw [Finset.lcm_eq_zero_iff] at h
      obtain ⟨m, hmF, hm0⟩ := h
      have h2 := hF m hmF
      simp only [id] at hm0
      omega
    · exact h
  refine Set.infinite_of_injective_forall_mem
    (f := fun j : ℤ => ((F.lcm id : ℕ) : ℤ) * j) ?_ ?_
  · intro j j' hjj'
    have hne : ((F.lcm id : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hlcm.ne'
    exact mul_left_cancel₀ hne hjj'
  · intro j
    simp only [Set.mem_setOf_eq]
    have := (jointObserver_periodic_iff F hF 0 (((F.lcm id : ℕ) : ℤ) * j)).mpr ⟨j, rfl⟩
    simpa using this

/-- **The cofinal doctrine family reconstructs the open lift.**  All congruence doctrines together
separate points of `ℤ`. -/
theorem cofinal_separating {n n' : ℤ} (h : ∀ m : ℕ, 2 ≤ m → (n : ZMod m) = (n' : ZMod m)) :
    n = n' := by
  by_contra hne
  have hdne : n - n' ≠ 0 := sub_ne_zero.mpr hne
  set m : ℕ := (n - n').natAbs + 2 with hm
  have hm2 : 2 ≤ m := by omega
  have hne0 : NeZero m := ⟨by omega⟩
  have h0 : (((n - n') : ℤ) : ZMod m) = 0 := by
    rw [Int.cast_sub, h m hm2, sub_self]
  have hdvd : ((m : ℕ) : ℤ) ∣ (n - n') := (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mp h0
  have hdvdnat : m ∣ (n - n').natAbs := (natCast_dvd_int m (n - n')).mp hdvd
  have hpos : 0 < (n - n').natAbs := Int.natAbs_pos.mpr hdne
  have hle : m ≤ (n - n').natAbs := Nat.le_of_dvd hpos hdvdnat
  omega

/-- **The cofinal intersection of the congruence doctrines is the equality relation.** -/
theorem modDoctrine_iInf_eq_bot :
    ⨅ m : {m : ℕ // 2 ≤ m}, modDoctrine m.1 = ⊥ := by
  refine Setoid.ext fun a b => ?_
  rw [Setoid.bot_def]
  constructor
  · intro h
    refine cofinal_separating fun m hm => ?_
    have := (Setoid.le_def.mp (iInf_le (fun m : {m : ℕ // 2 ≤ m} => modDoctrine m.1) ⟨m, hm⟩)) h
    exact this
  · rintro rfl
    exact Setoid.refl' _ _

end Recurrence

section PhaseDoctrine

/-- The positive-modulus reader on the nonzero complex numbers. -/
noncomputable def modulusReader (z : ℂˣ) : {r : ℝ // 0 < r} :=
  ⟨‖(z : ℂ)‖, norm_pos_iff.mpr z.ne_zero⟩

/-- The phase doctrine: two nonzero complex numbers are indistinguishable exactly when they have
the same modulus. -/
noncomputable def phaseDoctrine : Setoid ℂˣ := Setoid.ker modulusReader

theorem modulusReader_surjective : Function.Surjective modulusReader := by
  intro r
  have hr : ((r : ℝ) : ℂ) ≠ 0 := by
    simpa using ne_of_gt r.2
  refine ⟨Units.mk0 ((r : ℝ) : ℂ) hr, ?_⟩
  apply Subtype.ext
  simp [modulusReader, abs_of_pos r.2]

/-- **The phase-doctrine quotient is exactly the positive reals.** -/
noncomputable def phaseQuotientEquiv : Quotient phaseDoctrine ≃ {r : ℝ // 0 < r} :=
  Setoid.quotientKerEquivOfSurjective modulusReader modulusReader_surjective

/-- The unit represented by the `N`-fold determinant loop. -/
noncomputable def loopUnit (N : ℤ) (t : ℝ) : ℂˣ := Units.mk0 (loopHistory N t) (loopHistory_ne_zero N t)

/-- **The phase doctrine sees the winding loop as a constant history.** -/
theorem phaseDoctrine_loopUnit (N : ℤ) (t t' : ℝ) :
    phaseDoctrine (loopUnit N t) (loopUnit N t') := by
  show modulusReader _ = modulusReader _
  apply Subtype.ext
  simp only [modulusReader, loopUnit, Units.val_mk0, loopHistory]
  rw [loopSpeed_mul, loopSpeed_mul, Complex.norm_exp_ofReal_mul_I,
    Complex.norm_exp_ofReal_mul_I]

/-- **Positivity is one doctrine, not a universal consequence.**  The phase doctrine turns the
`N`-fold winding loop into a constant history while its logarithmic lift stays open. -/
theorem phase_constant_lift_open {N : ℤ} (hN : N ≠ 0) :
    (∀ t t' : ℝ, phaseDoctrine (loopUnit N t) (loopUnit N t')) ∧ logLift N 1 ≠ logLift N 0 :=
  ⟨phaseDoctrine_loopUnit N, logLift_ne_of_ne_zero hN⟩

end PhaseDoctrine

section Capstone

/-- **The dynamic-equivalence law.**  Observer doctrines form a nondistributive lattice; every
finite congruence family sees the source translation as an exactly periodic history with infinite
fibres; the cofinal family separates points and so reconstructs the open lift. -/
theorem dynamic_equivalence_law (F : Finset ℕ) (hF : ∀ m ∈ F, 2 ≤ m) :
    (pointDoctrine 2 ⊓ (pointDoctrine 1 ⊔ pointDoctrine 0) ≠
        (pointDoctrine 2 ⊓ pointDoctrine 1) ⊔ (pointDoctrine 2 ⊓ pointDoctrine 0)) ∧
      (∀ n k : ℤ, jointObserver F (n + k) = jointObserver F n ↔ ((F.lcm id : ℕ) : ℤ) ∣ k) ∧
      {n : ℤ | jointObserver F n = jointObserver F 0}.Infinite ∧
      ⨅ m : {m : ℕ // 2 ≤ m}, modDoctrine m.1 = ⊥ :=
  ⟨doctrine_not_distributive, jointObserver_periodic_iff F hF,
    jointObserver_fibre_infinite F hF, modDoctrine_iInf_eq_bot⟩

end Capstone

end GaloisForLFunctions.HTGeometry
