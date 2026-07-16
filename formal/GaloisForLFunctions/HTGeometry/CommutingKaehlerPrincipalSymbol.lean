import GaloisForLFunctions.HTGeometry.HypertranscendentalKaehlerClockSymbol
import GaloisForLFunctions.HTGeometry.DirectionalKaehlerWedge

/-!
# Commuting Kähler principal-symbol superposition

For two commuting derivations, ordinary differential algebraicity of one element in each pure
direction forces ordinary differential algebraicity in every linear-combination direction.

The proof does not assume a finite mixed state and does not divide by separants.  Each derivation
induces a connection on relative Kähler differentials.  Pure differential algebraicity supplies a
positive-order monic recurrence for each connection orbit.  Commutation propagates both recurrences
across the mixed jet grid and traps the complete mixed orbit in one finite rectangle.  Every
directional Kähler orbit is therefore linearly dependent.

This is a field-theoretic, separant-free version of the finite-transcendence mechanism behind
multivariate D-algebraicity.  It is foundational infrastructure rather than a novelty claim.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Module Set

/-- Commuting field derivations induce commuting Lie derivatives on relative Kähler
differentials. -/
theorem kaehlerLieDifferential_commute
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (D E : Derivation K L L) (hcomm : Function.Commute D E) :
    Function.Commute (kaehlerLieDifferential D) (kaehlerLieDifferential E) := by
  intro w
  let V : Submodule L Ω[L⁄K] :=
    { carrier := {z |
        kaehlerLieDifferential D (kaehlerLieDifferential E z) =
          kaehlerLieDifferential E (kaehlerLieDifferential D z)}
      zero_mem' := by simp
      add_mem' := by
        intro x y hx hy
        simp only [Set.mem_setOf_eq, map_add]
        rw [hx, hy]
      smul_mem' := by
        intro a z hz
        simp only [Set.mem_setOf_eq]
        rw [kaehlerLieDifferential_smul, kaehlerLieDifferential_smul,
          map_add, map_add]
        simp only [kaehlerLieDifferential_smul]
        rw [hz, hcomm a]
        module }
  have hV : V = ⊤ := by
    apply top_unique
    rw [← KaehlerDifferential.span_range_derivation]
    apply Submodule.span_le.mpr
    rintro _ ⟨b, rfl⟩
    change KaehlerDifferential.D K L b ∈ V
    change kaehlerLieDifferential D
        (kaehlerLieDifferential E (KaehlerDifferential.D K L b)) =
      kaehlerLieDifferential E
        (kaehlerLieDifferential D (KaehlerDifferential.D K L b))
    simp only [kaehlerLieDifferential_D]
    exact congrArg (KaehlerDifferential.D K L) (hcomm b)
  change w ∈ V
  rw [hV]
  exact Submodule.mem_top

/-- Failure of algebraic independence of one ordinary jet orbit produces a positive-order monic
recurrence for its Kähler covectors.  The order is forced positive even when the root itself is
algebraic over the base. -/
theorem exists_pos_kaehlerLie_recurrence
    {K L : Type*} [Field K] [Field L] [Algebra K L] [CharZero K]
    (D : Derivation K L L) (x : L)
    (hdep : ¬ AlgebraicIndependent K
      (fun n : ℕ ↦ ((D : L → L)^[n]) x)) :
    ∃ m : ℕ, 0 < m ∧
      KaehlerDifferential.D K L (((D : L → L)^[m]) x) ∈
        Submodule.span L (Set.range fun i : Fin m ↦
          KaehlerDifferential.D K L (((D : L → L)^[(i : ℕ)]) x)) := by
  classical
  have hex : ∃ n : ℕ, ¬ AlgebraicIndependent K
      (fun j : Fin (n + 1) ↦ ((D : L → L)^[(j : ℕ)]) x) := by
    rw [algebraicIndependent_nat_iff_initialSegments] at hdep
    simpa only [not_forall] using hdep
  let m := Nat.find hex
  have hmdep : ¬ AlgebraicIndependent K
      (fun j : Fin (m + 1) ↦ ((D : L → L)^[(j : ℕ)]) x) :=
    Nat.find_spec hex
  by_cases hm : m = 0
  · rw [hm] at hmdep
    have hmdep0 : ¬ AlgebraicIndependent K
        (fun j : Fin 1 ↦ ((D : L → L)^[(j : ℕ)]) x) := by
      exact hmdep
    have hnotLI : ¬ LinearIndependent L
        (fun j : Fin 1 ↦
          KaehlerDifferential.D K L (((D : L → L)^[(j : ℕ)]) x)) := by
      intro hLI
      exact hmdep0 ((algebraicIndependent_iff_kaehlerD_linearIndependent _).2 hLI)
    have hdx : KaehlerDifferential.D K L x = 0 := by
      have hzero : (fun j : Fin 1 ↦
          KaehlerDifferential.D K L (((D : L → L)^[(j : ℕ)]) x)) default = 0 := by
        simpa only [linearIndependent_unique_iff, not_ne_iff] using hnotLI
      simpa using hzero
    refine ⟨1, by omega, ?_⟩
    have hnext : KaehlerDifferential.D K L (D x) = 0 := by
      rw [← kaehlerLieDifferential_D D x, hdx, map_zero]
    rw [show ((D : L → L)^[1]) x = D x by simp, hnext]
    exact Submodule.zero_mem _
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hprevAI : AlgebraicIndependent K
        (fun j : Fin m ↦ ((D : L → L)^[(j : ℕ)]) x) := by
      by_contra hprev
      have heq : m - 1 + 1 = m :=
        Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm)
      have hpred : ¬ AlgebraicIndependent K
          (fun j : Fin (m - 1 + 1) ↦ ((D : L → L)^[(j : ℕ)]) x) := by
        rw [heq]
        exact hprev
      exact (Nat.find_min hex (Nat.sub_lt hmpos Nat.zero_lt_one)) hpred
    have hprevLI : LinearIndependent L
        (fun j : Fin m ↦
          KaehlerDifferential.D K L (((D : L → L)^[(j : ℕ)]) x)) :=
      (algebraicIndependent_iff_kaehlerD_linearIndependent _).1 hprevAI
    have hfullNotLI : ¬ LinearIndependent L
        (fun j : Fin (m + 1) ↦
          KaehlerDifferential.D K L (((D : L → L)^[(j : ℕ)]) x)) := by
      intro hLI
      exact hmdep ((algebraicIndependent_iff_kaehlerD_linearIndependent _).2 hLI)
    have hlast :
        KaehlerDifferential.D K L (((D : L → L)^[m]) x) ∈
          Submodule.span L (Set.range fun j : Fin m ↦
            KaehlerDifferential.D K L (((D : L → L)^[(j : ℕ)]) x)) := by
      by_contra hnot
      apply hfullNotLI
      rw [linearIndependent_finSucc']
      constructor
      · simpa [Fin.init] using hprevLI
      · simpa using hnot
    exact ⟨m, hmpos, hlast⟩

/-- The mixed Kähler jet obtained by first applying the `E`-connection `j` times and then the
`D`-connection `i` times to `dx`. -/
def kaehlerMixedJet
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (D E : Derivation K L L) (x : L) (i j : ℕ) : Ω[L⁄K] :=
  (kaehlerLieDifferential D)^[i]
    ((kaehlerLieDifferential E)^[j] (KaehlerDifferential.D K L x))

/-- The finite mixed principal-symbol rectangle of widths `m` and `n`. -/
def kaehlerJetRectangle
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (D E : Derivation K L L) (x : L) (m n : ℕ) : Submodule L Ω[L⁄K] :=
  Submodule.span L (Set.range fun q : Fin m × Fin n ↦
    kaehlerMixedJet D E x q.1 q.2)

theorem kaehlerMixedJet_succ_left
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (D E : Derivation K L L) (x : L) (i j : ℕ) :
    kaehlerLieDifferential D (kaehlerMixedJet D E x i j) =
      kaehlerMixedJet D E x (i + 1) j := by
  rw [kaehlerMixedJet, kaehlerMixedJet]
  simpa [Nat.add_comm] using
    (Function.iterate_succ_apply' (kaehlerLieDifferential D) i
      ((kaehlerLieDifferential E)^[j] (KaehlerDifferential.D K L x))).symm

theorem kaehlerMixedJet_succ_right
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (D E : Derivation K L L) (x : L) (i j : ℕ)
    (hcomm : Function.Commute D E) :
    kaehlerLieDifferential E (kaehlerMixedJet D E x i j) =
      kaehlerMixedJet D E x i (j + 1) := by
  have hLie := kaehlerLieDifferential_commute D E hcomm
  rw [kaehlerMixedJet, kaehlerMixedJet,
    ← (hLie.iterate_left i).eq]
  congr 1
  simpa [Nat.add_comm] using
    (Function.iterate_succ_apply' (kaehlerLieDifferential E) j
      (KaehlerDifferential.D K L x)).symm

/-- A Kähler connection maps the span of one generating set into another as soon as it does so on
generators and the target span already contains the source generators. -/
theorem kaehlerLie_mem_span_of_generators
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (D : Derivation K L L) (S T : Set Ω[L⁄K])
    (hST : S ⊆ Submodule.span L T)
    (hDT : ∀ w ∈ S, kaehlerLieDifferential D w ∈ Submodule.span L T)
    {w : Ω[L⁄K]} (hw : w ∈ Submodule.span L S) :
    kaehlerLieDifferential D w ∈ Submodule.span L T := by
  let V : Submodule L Ω[L⁄K] :=
    { carrier := {z | z ∈ Submodule.span L T ∧
          kaehlerLieDifferential D z ∈ Submodule.span L T}
      zero_mem' := by simp
      add_mem' := by
        intro a b ha hb
        exact ⟨Submodule.add_mem _ ha.1 hb.1, by
          rw [map_add]
          exact Submodule.add_mem _ ha.2 hb.2⟩
      smul_mem' := by
        intro a z hz
        refine ⟨Submodule.smul_mem _ a hz.1, ?_⟩
        rw [kaehlerLieDifferential_smul]
        exact Submodule.add_mem _
          (Submodule.smul_mem _ (D a) hz.1)
          (Submodule.smul_mem _ a hz.2) }
  have hSV : S ⊆ V := by
    intro z hz
    exact ⟨hST hz, hDT z hz⟩
  have hwV : w ∈ V := (Submodule.span_le.mpr hSV) hw
  exact hwV.2

theorem kaehlerJetRectangle_mono
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (D E : Derivation K L L) (x : L)
    {m n m' n' : ℕ} (hm : m ≤ m') (hn : n ≤ n') :
    kaehlerJetRectangle D E x m n ≤
      kaehlerJetRectangle D E x m' n' := by
  apply Submodule.span_mono
  rintro _ ⟨q, rfl⟩
  exact ⟨(⟨q.1, lt_of_lt_of_le q.1.isLt hm⟩,
    ⟨q.2, lt_of_lt_of_le q.2.isLt hn⟩), rfl⟩

theorem kaehlerLie_left_mem_nextRectangle
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (D E : Derivation K L L) (x : L) (m n : ℕ)
    {w : Ω[L⁄K]} (hw : w ∈ kaehlerJetRectangle D E x m n) :
    kaehlerLieDifferential D w ∈
      kaehlerJetRectangle D E x (m + 1) n := by
  apply kaehlerLie_mem_span_of_generators D
      (Set.range fun q : Fin m × Fin n ↦ kaehlerMixedJet D E x q.1 q.2)
      (Set.range fun q : Fin (m + 1) × Fin n ↦ kaehlerMixedJet D E x q.1 q.2)
  · rintro _ ⟨q, rfl⟩
    apply Submodule.subset_span
    exact ⟨(⟨q.1, lt_trans q.1.isLt (Nat.lt_succ_self m)⟩, q.2), rfl⟩
  · rintro _ ⟨q, rfl⟩
    rw [kaehlerMixedJet_succ_left]
    apply Submodule.subset_span
    exact ⟨(⟨q.1 + 1, Nat.add_lt_add_right q.1.isLt 1⟩, q.2), rfl⟩
  · exact hw

theorem kaehlerLie_right_mem_nextRectangle
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (D E : Derivation K L L) (x : L) (m n : ℕ)
    (hcomm : Function.Commute D E)
    {w : Ω[L⁄K]} (hw : w ∈ kaehlerJetRectangle D E x m n) :
    kaehlerLieDifferential E w ∈
      kaehlerJetRectangle D E x m (n + 1) := by
  apply kaehlerLie_mem_span_of_generators E
      (Set.range fun q : Fin m × Fin n ↦ kaehlerMixedJet D E x q.1 q.2)
      (Set.range fun q : Fin m × Fin (n + 1) ↦ kaehlerMixedJet D E x q.1 q.2)
  · rintro _ ⟨q, rfl⟩
    apply Submodule.subset_span
    exact ⟨(q.1, ⟨q.2, lt_trans q.2.isLt (Nat.lt_succ_self n)⟩), rfl⟩
  · rintro _ ⟨q, rfl⟩
    rw [kaehlerMixedJet_succ_right D E x q.1 q.2 hcomm]
    apply Submodule.subset_span
    exact ⟨(q.1, ⟨q.2 + 1, Nat.add_lt_add_right q.2.isLt 1⟩), rfl⟩
  · exact hw

/-- A terminal recurrence in the left direction propagates through every right-connection
layer. -/
theorem leftBoundary_propagates_across_rectangle
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (D E : Derivation K L L) (x : L) (m : ℕ)
    (hcomm : Function.Commute D E)
    (hboundary : kaehlerMixedJet D E x m 0 ∈
      kaehlerJetRectangle D E x m 1) :
    ∀ j : ℕ, kaehlerMixedJet D E x m j ∈
      kaehlerJetRectangle D E x m (j + 1) := by
  intro j
  induction j with
  | zero => simpa using hboundary
  | succ j ih =>
      have hnext := kaehlerLie_right_mem_nextRectangle
        D E x m (j + 1) hcomm ih
      rw [kaehlerMixedJet_succ_right D E x m j hcomm] at hnext
      simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hnext

/-- A terminal recurrence in the right direction propagates through every left-connection
layer. -/
theorem rightBoundary_propagates_across_rectangle
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (D E : Derivation K L L) (x : L) (n : ℕ)
    (hboundary : kaehlerMixedJet D E x 0 n ∈
      kaehlerJetRectangle D E x 1 n) :
    ∀ i : ℕ, kaehlerMixedJet D E x i n ∈
      kaehlerJetRectangle D E x (i + 1) n := by
  intro i
  induction i with
  | zero => simpa using hboundary
  | succ i ih =>
      have hnext := kaehlerLie_left_mem_nextRectangle
        D E x (i + 1) n ih
      rw [kaehlerMixedJet_succ_left D E x i n] at hnext
      simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hnext

/-- The mixed rectangle is invariant under the left connection once its pure recurrence is
installed. -/
theorem kaehlerJetRectangle_stable_left
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (D E : Derivation K L L) (x : L) (m n : ℕ)
    (hcomm : Function.Commute D E)
    (hboundary : kaehlerMixedJet D E x m 0 ∈
      kaehlerJetRectangle D E x m 1)
    {w : Ω[L⁄K]} (hw : w ∈ kaehlerJetRectangle D E x m n) :
    kaehlerLieDifferential D w ∈ kaehlerJetRectangle D E x m n := by
  apply kaehlerLie_mem_span_of_generators D
      (Set.range fun q : Fin m × Fin n ↦ kaehlerMixedJet D E x q.1 q.2)
      (Set.range fun q : Fin m × Fin n ↦ kaehlerMixedJet D E x q.1 q.2)
  · exact fun _ hz ↦ Submodule.subset_span hz
  · rintro _ ⟨q, rfl⟩
    rw [kaehlerMixedJet_succ_left]
    by_cases hi : q.1 + 1 < m
    · apply Submodule.subset_span
      exact ⟨(⟨q.1 + 1, hi⟩, q.2), rfl⟩
    · have hieq : q.1 + 1 = m := by omega
      rw [hieq]
      apply kaehlerJetRectangle_mono D E x (le_refl m)
        (Nat.succ_le_of_lt q.2.isLt)
      exact leftBoundary_propagates_across_rectangle
        D E x m hcomm hboundary q.2
  · exact hw

/-- The mixed rectangle is invariant under the right connection once its pure recurrence is
installed. -/
theorem kaehlerJetRectangle_stable_right
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (D E : Derivation K L L) (x : L) (m n : ℕ)
    (hcomm : Function.Commute D E)
    (hboundary : kaehlerMixedJet D E x 0 n ∈
      kaehlerJetRectangle D E x 1 n)
    {w : Ω[L⁄K]} (hw : w ∈ kaehlerJetRectangle D E x m n) :
    kaehlerLieDifferential E w ∈ kaehlerJetRectangle D E x m n := by
  apply kaehlerLie_mem_span_of_generators E
      (Set.range fun q : Fin m × Fin n ↦ kaehlerMixedJet D E x q.1 q.2)
      (Set.range fun q : Fin m × Fin n ↦ kaehlerMixedJet D E x q.1 q.2)
  · exact fun _ hz ↦ Submodule.subset_span hz
  · rintro _ ⟨q, rfl⟩
    rw [kaehlerMixedJet_succ_right D E x q.1 q.2 hcomm]
    by_cases hj : q.2 + 1 < n
    · apply Submodule.subset_span
      exact ⟨(q.1, ⟨q.2 + 1, hj⟩), rfl⟩
    · have hjeq : q.2 + 1 = n := by omega
      rw [hjeq]
      apply kaehlerJetRectangle_mono D E x
        (Nat.succ_le_of_lt q.1.isLt) (le_refl n)
      exact rightBoundary_propagates_across_rectangle
        D E x n hboundary q.1
  · exact hw

theorem kaehlerMixedJet_zero_right
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (D E : Derivation K L L) (x : L) :
    ∀ i : ℕ, kaehlerMixedJet D E x i 0 =
      KaehlerDifferential.D K L (((D : L → L)^[i]) x) := by
  intro i
  induction i with
  | zero => simp [kaehlerMixedJet]
  | succ i ih =>
      rw [← kaehlerMixedJet_succ_left D E x i 0, ih,
        kaehlerLieDifferential_D]
      congr 1
      exact (Function.iterate_succ_apply' D i x).symm

theorem kaehlerMixedJet_zero_left
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (D E : Derivation K L L) (x : L) :
    ∀ j : ℕ, kaehlerMixedJet D E x 0 j =
      KaehlerDifferential.D K L (((E : L → L)^[j]) x) := by
  intro j
  simp only [kaehlerMixedJet, Function.iterate_zero_apply]
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      calc
        kaehlerLieDifferential E
            ((kaehlerLieDifferential E)^[j] (KaehlerDifferential.D K L x)) =
            kaehlerLieDifferential E
              (KaehlerDifferential.D K L (((E : L → L)^[j]) x)) :=
          congrArg (kaehlerLieDifferential E) ih
        _ = KaehlerDifferential.D K L (E (((E : L → L)^[j]) x)) := by
          rw [kaehlerLieDifferential_D]
        _ = KaehlerDifferential.D K L (((E : L → L)^[j + 1]) x) := by
          congr 1
          exact (Function.iterate_succ_apply' E j x).symm

theorem leftBoundary_of_pure_recurrence
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (D E : Derivation K L L) (x : L) (m : ℕ)
    (hrec : KaehlerDifferential.D K L (((D : L → L)^[m]) x) ∈
      Submodule.span L (Set.range fun i : Fin m ↦
        KaehlerDifferential.D K L (((D : L → L)^[(i : ℕ)]) x))) :
    kaehlerMixedJet D E x m 0 ∈
      kaehlerJetRectangle D E x m 1 := by
  rw [kaehlerMixedJet_zero_right]
  apply (Submodule.span_mono ?_) hrec
  rintro _ ⟨i, rfl⟩
  change KaehlerDifferential.D K L (((D : L → L)^[(i : ℕ)]) x) ∈ _
  rw [← kaehlerMixedJet_zero_right D E x i]
  exact ⟨(i, default), rfl⟩

theorem rightBoundary_of_pure_recurrence
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (D E : Derivation K L L) (x : L) (n : ℕ)
    (hrec : KaehlerDifferential.D K L (((E : L → L)^[n]) x) ∈
      Submodule.span L (Set.range fun j : Fin n ↦
        KaehlerDifferential.D K L (((E : L → L)^[(j : ℕ)]) x))) :
    kaehlerMixedJet D E x 0 n ∈
      kaehlerJetRectangle D E x 1 n := by
  rw [kaehlerMixedJet_zero_left]
  apply (Submodule.span_mono ?_) hrec
  rintro _ ⟨j, rfl⟩
  change KaehlerDifferential.D K L (((E : L → L)^[(j : ℕ)]) x) ∈ _
  rw [← kaehlerMixedJet_zero_left D E x j]
  exact ⟨(default, j), rfl⟩

theorem kaehlerD_derivation_linearCombination
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (D E : Derivation K L L) (c d : K) (y : L) :
    KaehlerDifferential.D K L ((c • D + d • E) y) =
      c • kaehlerLieDifferential D (KaehlerDifferential.D K L y) +
        d • kaehlerLieDifferential E (KaehlerDifferential.D K L y) := by
  rw [Derivation.add_apply, Derivation.smul_apply, Derivation.smul_apply,
    map_add]
  change (KaehlerDifferential.D K L).toLinearMap (c • D y) +
      (KaehlerDifferential.D K L).toLinearMap (d • E y) = _
  rw [map_smul, map_smul,
    kaehlerLieDifferential_D, kaehlerLieDifferential_D]
  rfl

/-- **Finite-rectangle principal-symbol theorem.**  Positive pure recurrences for two commuting
Kähler connections force every mixed Kähler jet into the single `m × n` rectangle. -/
theorem kaehlerMixedJet_mem_rectangle
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (D E : Derivation K L L) (x : L) (m n : ℕ)
    (hmpos : 0 < m) (hnpos : 0 < n)
    (hcomm : Function.Commute D E)
    (hmrec : KaehlerDifferential.D K L (((D : L → L)^[m]) x) ∈
      Submodule.span L (Set.range fun i : Fin m ↦
        KaehlerDifferential.D K L (((D : L → L)^[(i : ℕ)]) x)))
    (hnrec : KaehlerDifferential.D K L (((E : L → L)^[n]) x) ∈
      Submodule.span L (Set.range fun j : Fin n ↦
        KaehlerDifferential.D K L (((E : L → L)^[(j : ℕ)]) x))) :
    ∀ i j : ℕ, kaehlerMixedJet D E x i j ∈ kaehlerJetRectangle D E x m n := by
  have hmBoundary := leftBoundary_of_pure_recurrence D E x m hmrec
  have hnBoundary := rightBoundary_of_pure_recurrence D E x n hnrec
  let W := kaehlerJetRectangle D E x m n
  have hroot : kaehlerMixedJet D E x 0 0 ∈ W := by
    apply Submodule.subset_span
    exact ⟨(⟨0, hmpos⟩, ⟨0, hnpos⟩), rfl⟩
  have hstableD : ∀ w ∈ W, kaehlerLieDifferential D w ∈ W := by
    intro w hw
    exact kaehlerJetRectangle_stable_left
      D E x m n hcomm hmBoundary hw
  have hstableE : ∀ w ∈ W, kaehlerLieDifferential E w ∈ W := by
    intro w hw
    exact kaehlerJetRectangle_stable_right
      D E x m n hcomm hnBoundary hw
  have hrow : ∀ j : ℕ, kaehlerMixedJet D E x 0 j ∈ W := by
    intro j
    induction j with
    | zero => exact hroot
    | succ j ih =>
        rw [← kaehlerMixedJet_succ_right D E x 0 j hcomm]
        exact hstableE _ ih
  intro i j
  induction i with
  | zero => exact hrow j
  | succ i ih =>
      rw [← kaehlerMixedJet_succ_left D E x i j]
      exact hstableD _ ih

/-- The principal-symbol rectangle has dimension at most the product of its two recurrence
orders. -/
theorem finrank_kaehlerJetRectangle_le
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (D E : Derivation K L L) (x : L) (m n : ℕ) :
    Module.finrank L (kaehlerJetRectangle D E x m n) ≤ m * n := by
  letI : Module.Finite L (kaehlerJetRectangle D E x m n) := by
    dsimp [kaehlerJetRectangle]
    exact Module.Finite.span_of_finite L (Set.finite_range fun q : Fin m × Fin n ↦
      kaehlerMixedJet D E x q.1 q.2)
  simpa [kaehlerJetRectangle] using
    (finrank_range_le_card (R := L)
      (fun q : Fin m × Fin n ↦ kaehlerMixedJet D E x q.1 q.2))

/-- **Commuting Kähler principal-symbol superposition.**  If one element is ordinarily
differentially algebraic for each of two commuting derivations, then it is ordinarily
differentially algebraic for every constant linear combination of them.  The finite mixed
principal-symbol rectangle is derived inside the proof; it is not a hypothesis. -/
theorem commutingDerivations_superposition
    {K L : Type*} [Field K] [Field L] [Algebra K L] [CharZero K]
    (D E : Derivation K L L) (x : L)
    (hcomm : Function.Commute D E)
    (hD : ¬ AlgebraicIndependent K (fun r : ℕ ↦ ((D : L → L)^[r]) x))
    (hE : ¬ AlgebraicIndependent K (fun r : ℕ ↦ ((E : L → L)^[r]) x)) :
    ∀ c d : K, ¬ AlgebraicIndependent K
      (fun r : ℕ ↦ (((c • D + d • E : Derivation K L L) : L → L)^[r]) x) := by
  classical
  obtain ⟨m, hmpos, hmrec⟩ := exists_pos_kaehlerLie_recurrence D x hD
  obtain ⟨n, hnpos, hnrec⟩ := exists_pos_kaehlerLie_recurrence E x hE
  have hmBoundary := leftBoundary_of_pure_recurrence D E x m hmrec
  have hnBoundary := rightBoundary_of_pure_recurrence D E x n hnrec
  let W := kaehlerJetRectangle D E x m n
  letI : Module.Finite L W := by
    dsimp [W, kaehlerJetRectangle]
    exact Module.Finite.span_of_finite L (Set.finite_range fun q : Fin m × Fin n ↦
      kaehlerMixedJet D E x q.1 q.2)
  have hroot : KaehlerDifferential.D K L x ∈ W := by
    apply Submodule.subset_span
    have hm0 : (0 : ℕ) < m := hmpos
    have hn0 : (0 : ℕ) < n := hnpos
    exact ⟨(⟨0, hm0⟩, ⟨0, hn0⟩), by simp [kaehlerMixedJet]⟩
  have hstableD : ∀ w ∈ W, kaehlerLieDifferential D w ∈ W := by
    intro w hw
    exact kaehlerJetRectangle_stable_left
      D E x m n hcomm hmBoundary hw
  have hstableE : ∀ w ∈ W, kaehlerLieDifferential E w ∈ W := by
    intro w hw
    exact kaehlerJetRectangle_stable_right
      D E x m n hcomm hnBoundary hw
  intro c d
  let F : Derivation K L L := c • D + d • E
  let y : ℕ → L := fun r ↦ ((F : L → L)^[r]) x
  have hy : ∀ r, KaehlerDifferential.D K L (y r) ∈ W := by
    intro r
    induction r with
    | zero => simpa [y] using hroot
    | succ r ih =>
        have hDr := hstableD _ ih
        have hEr := hstableE _ ih
        have hsum :
            c • kaehlerLieDifferential D (KaehlerDifferential.D K L (y r)) +
                d • kaehlerLieDifferential E (KaehlerDifferential.D K L (y r)) ∈ W := by
          exact Submodule.add_mem W
            (by simpa [Algebra.smul_def] using
              W.smul_mem (algebraMap K L c) hDr)
            (by simpa [Algebra.smul_def] using
              W.smul_mem (algebraMap K L d) hEr)
        change KaehlerDifferential.D K L (((F : L → L)^[r + 1]) x) ∈ W
        rw [Function.iterate_succ_apply']
        change KaehlerDifferential.D K L ((c • D + d • E) (y r)) ∈ W
        rw [kaehlerD_derivation_linearCombination]
        exact hsum
  intro hAI
  have hLI : LinearIndependent L
      (fun r : ℕ ↦ KaehlerDifferential.D K L (y r)) :=
    (algebraicIndependent_iff_kaehlerD_linearIndependent _).1 (by simpa [y, F] using hAI)
  let yW : ℕ → W := fun r ↦ ⟨KaehlerDifferential.D K L (y r), hy r⟩
  have hLIW : LinearIndependent L yW := by
    apply LinearIndependent.of_comp W.subtype
    simpa [yW, Function.comp_def] using hLI
  exact Module.Finite.not_linearIndependent_of_infinite yW hLIW

end

end GaloisForLFunctions.HTGeometry
