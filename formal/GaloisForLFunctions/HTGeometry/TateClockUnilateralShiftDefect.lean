import GaloisForLFunctions.HTGeometry.HypertranscendentalClockBoundary

/-!
# Unilateral-shift defect of the algebraic Tate clock

The forward Ind clock and backward Pro clock already form the adjoint pair underlying the
hypertranscendental clock boundary.  This file adds their canonical partial inverses and evaluates
the failure of two-sided invertibility exactly: both failures are the one-dimensional boundary
projector at clock coordinate zero.

This is the algebraic value pattern of the Susskind--Glogower unilateral quantum phase operator.
K. Fujikawa, *Phase Operator for the Photon Field and an Index Theorem*, arXiv:hep-th/9411066,
identifies its unit index and rank-one anomalous boundary.  The formal results below use that
operator-theoretic pattern only as a source of exact relations; the Tate-clock maps remain static
Ind/Pro observability maps, not temporal evolution operators.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped BigOperators

/-- Backward shift on the finitely supported Ind clock. -/
def tateClockIndBackward {K : Type*} [Zero K]
    (a : ℕ →₀ K) : ℕ →₀ K :=
  Finsupp.comapDomain tateClockSucc a tateClockSucc.injective.injOn

@[simp] theorem tateClockIndBackward_apply
    {K : Type*} [Zero K] (a : ℕ →₀ K) (n : ℕ) :
    tateClockIndBackward a n = a (n + 1) := by
  simp [tateClockIndBackward, tateClockSucc, Finsupp.comapDomain_apply]

/-- Backward observation is a left inverse of forward Ind extension. -/
theorem tateClockIndBackward_forward
    {K : Type*} [Zero K] (a : ℕ →₀ K) :
    tateClockIndBackward (tateClockIndForward a) = a := by
  ext n
  simp

/-- Rank-one boundary projector on the Ind clock. -/
def tateClockIndBoundaryProjector {K : Type*} [Zero K]
    (a : ℕ →₀ K) : ℕ →₀ K :=
  Finsupp.single 0 (a 0)

@[simp] theorem tateClockIndBoundaryProjector_apply_zero
    {K : Type*} [Zero K] (a : ℕ →₀ K) :
    tateClockIndBoundaryProjector a 0 = a 0 := by
  simp [tateClockIndBoundaryProjector]

@[simp] theorem tateClockIndBoundaryProjector_apply_succ
    {K : Type*} [Zero K] (a : ℕ →₀ K) (n : ℕ) :
    tateClockIndBoundaryProjector a (n + 1) = 0 := by
  simp [tateClockIndBoundaryProjector]

/-- **Ind unilateral-shift defect.**  Forward after backward observation loses exactly the
boundary coordinate and no bulk observable. -/
theorem tateClockIndForward_backward_eq_sub_boundary
    {K : Type*} [AddCommGroup K] (a : ℕ →₀ K) :
    tateClockIndForward (tateClockIndBackward a) =
      a - tateClockIndBoundaryProjector a := by
  ext n
  cases n with
  | zero => simp
  | succ n => simp

/-- Every finite clock covector splits canonically into its boundary reading and a shifted bulk
covector. -/
theorem tateClockInd_boundary_add_forward_backward
    {K : Type*} [AddCommGroup K] (a : ℕ →₀ K) :
    tateClockIndBoundaryProjector a +
        tateClockIndForward (tateClockIndBackward a) = a := by
  rw [tateClockIndForward_backward_eq_sub_boundary]
  abel

/-- Zero-extending forward shift on the linearly compact Pro clock. -/
def tateClockProForward {K : Type*} [Zero K] (p : ℕ → K) : ℕ → K
  | 0 => 0
  | n + 1 => p n

@[simp] theorem tateClockProForward_apply_zero
    {K : Type*} [Zero K] (p : ℕ → K) :
    tateClockProForward p 0 = 0 := rfl

@[simp] theorem tateClockProForward_apply_succ
    {K : Type*} [Zero K] (p : ℕ → K) (n : ℕ) :
    tateClockProForward p (n + 1) = p n := rfl

/-- Backward Pro observation is a right inverse of forward zero extension. -/
theorem tateClockProBackward_forward
    {K : Type*} [Zero K] (p : ℕ → K) :
    tateClockProBackward (tateClockProForward p) = p := by
  funext n
  rfl

/-- **Pro unilateral-shift defect.**  Forward after backward observation removes exactly the
one-dimensional Pro boundary already classified by `tateClockProBackward_eq_zero_iff_exists_boundary`. -/
theorem tateClockProForward_backward_eq_sub_boundary
    {K : Type*} [AddCommGroup K] (p : ℕ → K) :
    tateClockProForward (tateClockProBackward p) =
      p - tateClockProBoundary (p 0) := by
  funext n
  cases n with
  | zero => simp [tateClockProBoundary]
  | succ n => simp [tateClockProBackward, tateClockProBoundary]

/-- Every Pro clock state splits into its boundary line and a forward-shifted observable tail. -/
theorem tateClockPro_boundary_add_forward_backward
    {K : Type*} [AddCommGroup K] (p : ℕ → K) :
    tateClockProBoundary (p 0) +
        tateClockProForward (tateClockProBackward p) = p := by
  rw [tateClockProForward_backward_eq_sub_boundary]
  abel

/-- **Boundary-plus-bulk clock value relation.**  Every Ind/Pro observable pairing is the sum of
one boundary reading and the pairing of the two shifted tails.  This is the exact value-level
content of the unilateral-clock defect. -/
theorem tateClockPairing_boundary_add_shift
    {K : Type*} [CommRing K] (a : ℕ →₀ K) (p : ℕ → K) :
    tateClockPairing a p =
      a 0 * p 0 +
        tateClockPairing (tateClockIndBackward a) (tateClockProBackward p) := by
  nth_rewrite 1 [← tateClockInd_boundary_add_forward_backward a]
  calc
    tateClockPairing
        (tateClockIndBoundaryProjector a +
          tateClockIndForward (tateClockIndBackward a)) p =
        tateClockPairing (tateClockIndBoundaryProjector a) p +
          tateClockPairing (tateClockIndForward (tateClockIndBackward a)) p := by
            simp only [tateClockPairing]
            apply Finsupp.sum_add_index
            · intro n hn
              simp
            · intro n hn x y
              exact add_mul x y (p n)
    _ = a 0 * p 0 +
        tateClockPairing (tateClockIndBackward a) (tateClockProBackward p) := by
          rw [tateClockPairing_indForward]
          simp [tateClockPairing, tateClockIndBoundaryProjector]

/-- The `m`-fold forward extension on the finitely supported Ind clock. -/
def tateClockIndForwardN {K : Type*} [Zero K] :
    ℕ → (ℕ →₀ K) → (ℕ →₀ K)
  | 0, a => a
  | m + 1, a => tateClockIndForward (tateClockIndForwardN m a)

/-- The `m`-fold backward observation on the finitely supported Ind clock. -/
def tateClockIndBackwardN {K : Type*} [Zero K] :
    ℕ → (ℕ →₀ K) → (ℕ →₀ K)
  | 0, a => a
  | m + 1, a => tateClockIndBackwardN m (tateClockIndBackward a)

/-- The `m`-fold backward observation on the Pro clock. -/
def tateClockProBackwardN {K : Type*} :
    ℕ → (ℕ → K) → (ℕ → K)
  | 0, p => p
  | m + 1, p => tateClockProBackwardN m (tateClockProBackward p)

@[simp] theorem tateClockIndBackwardN_apply
    {K : Type*} [Zero K] (m : ℕ) (a : ℕ →₀ K) (n : ℕ) :
    tateClockIndBackwardN m a n = a (n + m) := by
  induction m generalizing a n with
  | zero => simp [tateClockIndBackwardN]
  | succ m ih =>
      rw [tateClockIndBackwardN, ih, tateClockIndBackward_apply]
      congr 1

@[simp] theorem tateClockProBackwardN_apply
    {K : Type*} (m : ℕ) (p : ℕ → K) (n : ℕ) :
    tateClockProBackwardN m p n = p (n + m) := by
  induction m generalizing p n with
  | zero => simp [tateClockProBackwardN]
  | succ m ih =>
      rw [tateClockProBackwardN, ih]
      rfl

theorem tateClockIndForwardN_apply
    {K : Type*} [Zero K] (m : ℕ) (a : ℕ →₀ K) (n : ℕ) :
    tateClockIndForwardN m a n = if m ≤ n then a (n - m) else 0 := by
  induction m generalizing n with
  | zero => simp [tateClockIndForwardN]
  | succ m ih =>
      cases n with
      | zero => simp [tateClockIndForwardN]
      | succ n =>
          rw [tateClockIndForwardN, tateClockIndForward_apply_succ, ih]
          simp only [Nat.succ_le_succ_iff, Nat.succ_sub_succ_eq_sub]

/-- Backward observation remains a left inverse after any finite number of forward extensions. -/
theorem tateClockIndBackwardN_forwardN
    {K : Type*} [Zero K] (m : ℕ) (a : ℕ →₀ K) :
    tateClockIndBackwardN m (tateClockIndForwardN m a) = a := by
  ext n
  rw [tateClockIndBackwardN_apply, tateClockIndForwardN_apply]
  have hm : m ≤ n + m := by omega
  simp [hm]

/-- The oriented boundary interval cut out by an `m`-fold unilateral shift. It retains every
sector from charge `0` through charge `m - 1`, rather than only one endpoint. -/
def tateClockIndBoundaryInterval {K : Type*} [AddCommMonoid K]
    (m : ℕ) (a : ℕ →₀ K) : ℕ →₀ K :=
  ∑ k ∈ Finset.range m, Finsupp.single k (a k)

@[simp] theorem tateClockIndBoundaryInterval_apply
    {K : Type*} [AddCommMonoid K] (m : ℕ) (a : ℕ →₀ K) (n : ℕ) :
    tateClockIndBoundaryInterval m a n = if n < m then a n else 0 := by
  classical
  unfold tateClockIndBoundaryInterval
  rw [Finset.sum_apply']
  simp only [Finsupp.single_apply]
  by_cases hn : n < m
  · simp [hn]
  · simp [hn]

/-- **Finite unilateral interval decomposition.** Every Ind state is exactly its first `m`
boundary sectors plus the tail recovered after `m` backward and forward shifts. -/
theorem tateClockInd_boundaryInterval_add_forwardN_backwardN
    {K : Type*} [AddCommGroup K] (m : ℕ) (a : ℕ →₀ K) :
    tateClockIndBoundaryInterval m a +
        tateClockIndForwardN m (tateClockIndBackwardN m a) = a := by
  ext n
  simp only [Finsupp.add_apply]
  rw [tateClockIndBoundaryInterval_apply, tateClockIndForwardN_apply]
  by_cases hn : n < m
  · simp [hn, Nat.not_le_of_lt hn]
  · have hmn : m ≤ n := Nat.le_of_not_gt hn
    rw [if_neg hn, if_pos hmn, tateClockIndBackwardN_apply]
    simp only [zero_add]
    rw [Nat.sub_add_cancel hmn]

/-- **Oriented interval cocycle.** The boundary interval of a composite shift is the first
interval followed by the translated second interval. This retains the order of the crossings. -/
theorem tateClockIndBoundaryInterval_add
    {K : Type*} [AddCommMonoid K] (m n : ℕ) (a : ℕ →₀ K) :
    tateClockIndBoundaryInterval (m + n) a =
      tateClockIndBoundaryInterval m a +
        tateClockIndForwardN m
          (tateClockIndBoundaryInterval n (tateClockIndBackwardN m a)) := by
  ext i
  simp only [Finsupp.add_apply]
  rw [tateClockIndBoundaryInterval_apply, tateClockIndBoundaryInterval_apply,
    tateClockIndForwardN_apply]
  by_cases hi : i < m
  · have himn : i < m + n := by omega
    simp [hi, himn, Nat.not_le_of_lt hi]
  · have hmi : m ≤ i := Nat.le_of_not_gt hi
    rw [if_neg hi, if_pos hmi, tateClockIndBoundaryInterval_apply,
      tateClockIndBackwardN_apply]
    have hsub : i - m + m = i := Nat.sub_add_cancel hmi
    by_cases himn : i < m + n
    · have hin : i - m < n := by omega
      rw [if_pos himn, if_pos hin, hsub]
      simp
    · have hin : ¬i - m < n := by omega
      simp [himn, hin]

/-- **Finite boundary-plus-bulk pairing law.** The defect of `m` unilateral shifts is the whole
oriented interval of the first `m` pairings. -/
theorem tateClockPairing_boundaryInterval_add_shift
    {K : Type*} [CommRing K] (m : ℕ) (a : ℕ →₀ K) (p : ℕ → K) :
    tateClockPairing a p =
      (∑ k ∈ Finset.range m, a k * p k) +
        tateClockPairing (tateClockIndBackwardN m a) (tateClockProBackwardN m p) := by
  induction m generalizing a p with
  | zero => simp [tateClockIndBackwardN, tateClockProBackwardN]
  | succ m ih =>
      calc
        tateClockPairing a p =
            a 0 * p 0 + tateClockPairing
              (tateClockIndBackward a) (tateClockProBackward p) :=
          tateClockPairing_boundary_add_shift a p
        _ = a 0 * p 0 +
            ((∑ k ∈ Finset.range m,
                tateClockIndBackward a k * tateClockProBackward p k) +
              tateClockPairing
                (tateClockIndBackwardN m (tateClockIndBackward a))
                (tateClockProBackwardN m (tateClockProBackward p))) := by rw [ih]
        _ = (∑ k ∈ Finset.range (m + 1), a k * p k) +
              tateClockPairing
                (tateClockIndBackwardN (m + 1) a)
                (tateClockProBackwardN (m + 1) p) := by
          rw [Finset.sum_range_succ']
          simp only [tateClockIndBackward_apply, tateClockProBackward,
            tateClockIndBackwardN, tateClockProBackwardN]
          abel

@[simp] theorem tateClockIndForwardN_single_zero
    {K : Type*} [Zero K] (m : ℕ) (c : K) :
    tateClockIndForwardN m (Finsupp.single 0 c) = Finsupp.single m c := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [tateClockIndForwardN, ih]
      ext n
      cases n with
      | zero => simp
      | succ n =>
          rw [tateClockIndForward_apply_succ]
          by_cases hmn : m = n
          · subst n
            simp
          · have hsucc : m + 1 ≠ n + 1 := by omega
            simp [hmn]

/-- The canonical one-sided tail filtration of the Ind clock.  Its `m`th term consists of
states whose first `m` coordinates vanish. -/
def tateClockIndTailSubmodule (K : Type*) [Field K] (m : ℕ) :
    Submodule K (ℕ →₀ K) where
  carrier := {a | ∀ n, n < m → a n = 0}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb n hn
    simp [ha n hn, hb n hn]
  smul_mem' := by
    intro c a ha n hn
    simp [ha n hn]

@[simp] theorem mem_tateClockIndTailSubmodule_iff
    {K : Type*} [Field K] (m : ℕ) (a : ℕ →₀ K) :
    a ∈ tateClockIndTailSubmodule K m ↔ ∀ n, n < m → a n = 0 :=
  Iff.rfl

/-- Forward extension preserves every level of the tail filtration. -/
theorem tateClockIndTailSubmodule_forward_mem
    {K : Type*} [Field K] (m : ℕ) {a : ℕ →₀ K}
    (ha : a ∈ tateClockIndTailSubmodule K m) :
    tateClockIndForward a ∈ tateClockIndTailSubmodule K m := by
  intro n hn
  cases n with
  | zero => simp
  | succ n =>
      rw [tateClockIndForward_apply_succ]
      exact ha n (by omega)

/-- Forward extension raises the tail filtration by one exact level. -/
theorem tateClockIndTailSubmodule_forward_mem_succ
    {K : Type*} [Field K] (m : ℕ) {a : ℕ →₀ K}
    (ha : a ∈ tateClockIndTailSubmodule K m) :
    tateClockIndForward a ∈ tateClockIndTailSubmodule K (m + 1) := by
  intro n hn
  cases n with
  | zero => simp
  | succ n =>
      rw [tateClockIndForward_apply_succ]
      exact ha n (by omega)

/-- Backward observation lowers the tail filtration by exactly one step. -/
theorem tateClockIndTailSubmodule_backward_mem
    {K : Type*} [Field K] (m : ℕ) {a : ℕ →₀ K}
    (ha : a ∈ tateClockIndTailSubmodule K (m + 1)) :
    tateClockIndBackward a ∈ tateClockIndTailSubmodule K m := by
  intro n hn
  rw [tateClockIndBackward_apply]
  exact ha (n + 1) (by omega)

/-- Every positive tail level is a nonzero proper submodule. -/
theorem tateClockIndTailSubmodule_nontrivial_proper
    {K : Type*} [Field K] (m : ℕ) :
    tateClockIndTailSubmodule K (m + 1) ≠ ⊥ ∧
      tateClockIndTailSubmodule K (m + 1) ≠ ⊤ := by
  constructor
  · intro hbot
    have hmem : Finsupp.single (m + 1) (1 : K) ∈
        tateClockIndTailSubmodule K (m + 1) := by
      intro n hn
      simp only [Finsupp.single_apply]
      split_ifs with h
      · subst n
        omega
      · rfl
    rw [hbot] at hmem
    simp at hmem
  · intro htop
    have hmem : Finsupp.single 0 (1 : K) ∈
        tateClockIndTailSubmodule K (m + 1) := by
      rw [htop]
      exact Submodule.mem_top
    have hzero := hmem 0 (by omega)
    simp at hzero

/-- A positive tail level is not preserved by backward observation.  Thus its nontriviality is
intrinsically polarized: it remembers the forward direction. -/
theorem tateClockIndTailSubmodule_not_backward_invariant
    {K : Type*} [Field K] (m : ℕ) :
    ¬∀ a ∈ tateClockIndTailSubmodule K (m + 1),
      tateClockIndBackward a ∈ tateClockIndTailSubmodule K (m + 1) := by
  intro hback
  have ha : Finsupp.single (m + 1) (1 : K) ∈
      tateClockIndTailSubmodule K (m + 1) := by
    intro n hn
    simp only [Finsupp.single_apply]
    split_ifs with h
    · subst n
      omega
    · rfl
  have hb := hback _ ha
  have hzero := hb m (by omega)
  rw [tateClockIndBackward_apply] at hzero
  simp at hzero

/-- The `m`th tail is exactly the kernel of the oriented interval observation. -/
theorem tateClockIndBoundaryInterval_eq_zero_iff_mem_tailSubmodule
    {K : Type*} [Field K] (m : ℕ) (a : ℕ →₀ K) :
    tateClockIndBoundaryInterval m a = 0 ↔
      a ∈ tateClockIndTailSubmodule K m := by
  constructor
  · intro hzero n hn
    have happly : tateClockIndBoundaryInterval m a n = 0 := by rw [hzero]; rfl
    rw [tateClockIndBoundaryInterval_apply, if_pos hn] at happly
    exact happly
  · intro ha
    ext n
    rw [tateClockIndBoundaryInterval_apply]
    by_cases hn : n < m
    · simp [hn, ha n hn]
    · simp [hn]

/-- The `m`th tail is exactly the range of the `m`-fold forward clock.  Hence the oriented
boundary interval is the finite quotient between the whole clock and this one-sided range. -/
theorem mem_tateClockIndTailSubmodule_iff_exists_forwardN
    {K : Type*} [Field K] (m : ℕ) (a : ℕ →₀ K) :
    a ∈ tateClockIndTailSubmodule K m ↔
      ∃ b : ℕ →₀ K, tateClockIndForwardN m b = a := by
  constructor
  · intro ha
    refine ⟨tateClockIndBackwardN m a, ?_⟩
    have hboundary : tateClockIndBoundaryInterval m a = 0 :=
      (tateClockIndBoundaryInterval_eq_zero_iff_mem_tailSubmodule m a).2 ha
    have hdecomp := tateClockInd_boundaryInterval_add_forwardN_backwardN m a
    rw [hboundary, zero_add] at hdecomp
    exact hdecomp
  · rintro ⟨b, rfl⟩
    intro n hn
    rw [tateClockIndForwardN_apply]
    simp [Nat.not_le_of_lt hn]

/-- **Two-sided descent no-go.**  A submodule of the finite Ind clock invariant under both
unilateral clock directions is either zero or the whole clock.  Consequently a nontrivial
algebraic/analytic descent cannot be encoded as a two-sided invariant subclock; it must retain a
polarization or live as relative comparison data. -/
theorem tateClockInd_bishiftInvariantSubmodule_eq_bot_or_top
    {K : Type*} [Field K] (D : Submodule K (ℕ →₀ K))
    (hforward : ∀ a ∈ D, tateClockIndForward a ∈ D)
    (hbackward : ∀ a ∈ D, tateClockIndBackward a ∈ D) :
    D = ⊥ ∨ D = ⊤ := by
  by_cases hbot : D = ⊥
  · exact Or.inl hbot
  right
  classical
  obtain ⟨a, haD, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  have hsupp : a.support.Nonempty := Finsupp.support_nonempty_iff.mpr ha0
  let N : ℕ := a.support.max' hsupp
  have hNmem : N ∈ a.support := Finset.max'_mem _ _
  have hN0 : a N ≠ 0 := Finsupp.mem_support_iff.mp hNmem
  have hforwardN : ∀ (m : ℕ) (b : ℕ →₀ K), b ∈ D → tateClockIndForwardN m b ∈ D := by
    intro m
    induction m with
    | zero =>
        intro b hb
        simpa [tateClockIndForwardN] using hb
    | succ m ih =>
        intro b hb
        rw [tateClockIndForwardN]
        exact hforward _ (ih b hb)
  have hbackwardN : ∀ (m : ℕ) (b : ℕ →₀ K), b ∈ D → tateClockIndBackwardN m b ∈ D := by
    intro m
    induction m with
    | zero =>
        intro b hb
        simpa [tateClockIndBackwardN] using hb
    | succ m ih =>
        intro b hb
        rw [tateClockIndBackwardN]
        exact ih _ (hbackward b hb)
  have htopExtract : tateClockIndBackwardN N a = Finsupp.single 0 (a N) := by
    ext n
    rw [tateClockIndBackwardN_apply]
    cases n with
    | zero => simp
    | succ n =>
        have hlt : N < n + 1 + N := by omega
        have hnot : n + 1 + N ∉ a.support := by
          intro hmem
          exact (not_lt_of_ge (a.support.le_max' _ hmem)) hlt
        rw [Finsupp.notMem_support_iff.mp hnot]
        simp
  have hsingle : Finsupp.single 0 (a N) ∈ D := by
    rw [← htopExtract]
    exact hbackwardN N a haD
  have he0 : Finsupp.single 0 (1 : K) ∈ D := by
    have hscaled := D.smul_mem ((a N)⁻¹) hsingle
    simpa [hN0] using hscaled
  have hunit : ∀ n : ℕ, Finsupp.single n (1 : K) ∈ D := by
    intro n
    have hn := hforwardN n (Finsupp.single 0 (1 : K)) he0
    simpa using hn
  apply Submodule.eq_top_iff'.2
  intro b
  induction b using Finsupp.induction with
  | zero => exact D.zero_mem
  | single_add n c b _ _ ih =>
      exact D.add_mem (by simpa using D.smul_mem c (hunit n)) ih

end

end GaloisForLFunctions.HTGeometry
