import GaloisForLFunctions.HTGeometry.ExponentialJetMap
import GaloisForLFunctions.HTGeometry.TriangularSolveContinuity

/-!
# The exponential jet map is open

The jet map of an exponential is triangular with nonvanishing diagonal `exp(y_0)`, so its inverse is
obtained by reading the system in order and dividing.  Choosing the logarithm of the zeroth entry
*relative to the base point* -- `y_0 + log(v / exp y_0)` -- makes that branch continuous near the
base value without any global cut, and the triangular solution is continuous in its data.

The jet map therefore carries neighbourhoods to neighbourhoods.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A jet sequence assembled from a prescribed zeroth entry and the higher entries. -/
def expJetExtend (a : ℂ) (u : ℕ → ℂ) : ℕ → ℂ := fun j => if j = 0 then a else u (j - 1)

@[simp]
theorem expJetExtend_zero (a : ℂ) (u : ℕ → ℂ) : expJetExtend a u 0 = a := by
  simp [expJetExtend]

@[simp]
theorem expJetExtend_succ (a : ℂ) (u : ℕ → ℂ) (j : ℕ) : expJetExtend a u (j + 1) = u j := by
  simp [expJetExtend]

theorem expJetExtend_self (y : ℕ → ℂ) : expJetExtend (y 0) (fun j => y (j + 1)) = y := by
  funext j
  cases j with
  | zero => simp
  | succ l => simp

/-- The lower part of the exponential jet system at a prescribed zeroth entry. -/
def expJetLower (a : ℂ) (k : ℕ) (u : ℕ → ℂ) : ℂ :=
  expJetScalar (expJetExtend a u) (k + 1) - Complex.exp a * u k

theorem expJetLower_congr (a : ℂ) (k : ℕ) (u u' : ℕ → ℂ) (h : ∀ j, j < k → u j = u' j) :
    expJetLower a k u = expJetLower a k u' := by
  have hcoord : ∀ j, j ≤ k → expJetExtend a u j = expJetExtend a u' j := by
    intro j hj
    cases j with
    | zero => simp
    | succ l =>
        rw [expJetExtend_succ, expJetExtend_succ, h l (by omega)]
  have hstep := expJetScalar_succ_sub_diagonal k (expJetExtend a u) (expJetExtend a u') hcoord
  simp only [expJetExtend_zero, expJetExtend_succ] at hstep
  simpa [expJetLower] using hstep

/-- The branch of the logarithm passing through a prescribed base value. -/
def logBranch (a v : ℂ) : ℂ := a + Complex.log (v / Complex.exp a)

theorem exp_logBranch {a v : ℂ} (hv : v ≠ 0) : Complex.exp (logBranch a v) = v := by
  rw [logBranch, Complex.exp_add, Complex.exp_log (div_ne_zero hv (Complex.exp_ne_zero a))]
  field_simp

@[simp]
theorem logBranch_exp (a : ℂ) : logBranch a (Complex.exp a) = a := by
  rw [logBranch, div_self (Complex.exp_ne_zero a), Complex.log_one, add_zero]

/-- The inverse of the exponential jet map, through the branch based at `a`. -/
def expJetInv (a : ℂ) (w : ℕ → ℂ) : ℕ → ℂ :=
  expJetExtend (logBranch a (w 0))
    (triangularSolve (Complex.exp (logBranch a (w 0))) (expJetLower (logBranch a (w 0)))
      fun k => w (k + 1))

@[simp]
theorem expJetInv_zero (a : ℂ) (w : ℕ → ℂ) : expJetInv a w 0 = logBranch a (w 0) := by
  simp [expJetInv]

/-- **The inverse really inverts.**  Every packet with nonzero zeroth entry is the exponential jet
packet of its inverse. -/
theorem expJetScalar_expJetInv {a : ℂ} {w : ℕ → ℂ} (hw : w 0 ≠ 0) (k : ℕ) :
    expJetScalar (expJetInv a w) k = w k := by
  set b : ℂ := logBranch a (w 0) with hb
  have hbexp : Complex.exp b = w 0 := exp_logBranch hw
  have hd : Complex.exp b ≠ 0 := Complex.exp_ne_zero b
  cases k with
  | zero =>
      rw [expJetScalar_zero, expJetInv_zero, ← hb]
      exact hbexp
  | succ k =>
      have hspec := triangularSolve_spec hd (expJetLower b) (expJetLower_congr b)
        (fun k => w (k + 1)) k
      have hexpand : expJetLower b k
          (triangularSolve (Complex.exp b) (expJetLower b) fun k => w (k + 1))
          = expJetScalar (expJetInv a w) (k + 1)
            - Complex.exp b *
              (triangularSolve (Complex.exp b) (expJetLower b) fun k => w (k + 1)) k := by
        rw [expJetLower]
        rfl
      rw [hexpand] at hspec
      linear_combination hspec

/-- **The inverse is a left inverse at the base point.** -/
theorem expJetInv_expJetScalar (y : ℕ → ℂ) (k : ℕ) :
    expJetInv (y 0) (fun j => expJetScalar y j) k = y k := by
  have h0 : expJetScalar y 0 = Complex.exp (y 0) := expJetScalar_zero y
  have hb : logBranch (y 0) (expJetScalar y 0) = y 0 := by
    rw [h0, logBranch_exp]
  have hd : Complex.exp (y 0) ≠ 0 := Complex.exp_ne_zero (y 0)
  have hsol : ∀ m, Complex.exp (y 0) * y (m + 1) + expJetLower (y 0) m (fun j => y (j + 1))
      = expJetScalar y (m + 1) := by
    intro m
    rw [expJetLower, expJetExtend_self]
    ring
  have huniq := fun m => triangularSolve_unique hd (expJetLower (y 0)) (expJetLower_congr (y 0))
    (fun m => expJetScalar y (m + 1)) (fun j => y (j + 1)) hsol m
  cases k with
  | zero =>
      rw [expJetInv_zero, hb]
  | succ k =>
      rw [expJetInv, hb, expJetExtend_succ, ← huniq k]

/-! ## Continuity -/

theorem continuousOn_expJetScalar {X : Type*} [TopologicalSpace X] {V : Set X}
    {Y : X → ℕ → ℂ} (hY : ∀ j, ContinuousOn (fun x => Y x j) V) (k : ℕ) :
    ContinuousOn (fun x => expJetScalar (Y x) k) V := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
      cases k with
      | zero =>
          simp only [expJetScalar_zero]
          exact Complex.continuous_exp.comp_continuousOn (hY 0)
      | succ k =>
          simp only [expJetScalar_succ]
          refine continuousOn_finsetSum _ fun i hi => ?_
          rw [Finset.mem_range] at hi
          exact (continuousOn_const.mul (ih i (by omega))).mul (hY (k - i + 1))

/-- The base-point branch is continuous where the rescaled zeroth entry avoids the cut. -/
theorem continuousOn_logBranch (a : ℂ) :
    ContinuousOn (fun w : ℕ → ℂ => logBranch a (w 0))
      {w : ℕ → ℂ | w 0 / Complex.exp a ∈ Complex.slitPlane} := by
  refine continuousOn_const.add (ContinuousOn.clog ?_ ?_)
  · exact ((continuous_apply (0 : ℕ)).continuousOn).div continuousOn_const
      fun _ _ => Complex.exp_ne_zero a
  · intro w hw
    exact hw

theorem continuousOn_expJetInv (a : ℂ) (k : ℕ) :
    ContinuousOn (fun w : ℕ → ℂ => expJetInv a w k)
      {w : ℕ → ℂ | w 0 / Complex.exp a ∈ Complex.slitPlane} := by
  set V : Set (ℕ → ℂ) := {w : ℕ → ℂ | w 0 / Complex.exp a ∈ Complex.slitPlane} with hV
  have hbranch : ContinuousOn (fun w : ℕ → ℂ => logBranch a (w 0)) V := continuousOn_logBranch a
  have hd : ContinuousOn (fun w : ℕ → ℂ => Complex.exp (logBranch a (w 0))) V :=
    Complex.continuous_exp.comp_continuousOn hbranch
  have hdne : ∀ w ∈ V, Complex.exp (logBranch a (w 0)) ≠ 0 := fun w _ => Complex.exp_ne_zero _
  have hsolve : ∀ m, ContinuousOn (fun w : ℕ → ℂ =>
      triangularSolve (Complex.exp (logBranch a (w 0))) (expJetLower (logBranch a (w 0)))
        (fun j => w (j + 1)) m) V := by
    intro m
    refine continuousOn_triangularSolve hd hdne ?_ (fun j => (continuous_apply (j + 1)).continuousOn)
      m
    intro j u hu
    rw [show (fun w : ℕ → ℂ => expJetLower (logBranch a (w 0)) j (u w))
        = fun w : ℕ → ℂ =>
          expJetScalar (expJetExtend (logBranch a (w 0)) (u w)) (j + 1)
            - Complex.exp (logBranch a (w 0)) * u w j from rfl]
    refine ContinuousOn.sub ?_ (hd.mul (hu j))
    refine continuousOn_expJetScalar (fun l => ?_) (j + 1)
    cases l with
    | zero => simpa using hbranch
    | succ l => simpa using hu l
  cases k with
  | zero =>
      simpa using hbranch
  | succ k =>
      simpa [expJetInv] using hsolve k

/-! ## Openness -/

/-- **The exponential jet map carries neighbourhoods to neighbourhoods.** -/
theorem expJetScalar_image_mem_nhds (y : ℕ → ℂ) {N : Set (ℕ → ℂ)} (hN : N ∈ nhds y) :
    (fun v : ℕ → ℂ => fun k => expJetScalar v k) '' N
      ∈ nhds (fun k => expJetScalar y k) := by
  classical
  set a : ℂ := y 0 with ha
  set V : Set (ℕ → ℂ) := {w : ℕ → ℂ | w 0 / Complex.exp a ∈ Complex.slitPlane} with hV
  have hVopen : IsOpen V := by
    refine (Complex.isOpen_slitPlane.preimage ?_)
    exact (continuous_apply (0 : ℕ)).div_const _
  have hΦy : (fun k => expJetScalar y k) ∈ V := by
    have h0 : expJetScalar y 0 = Complex.exp a := expJetScalar_zero y
    simp only [hV, Set.mem_setOf_eq, h0, div_self (Complex.exp_ne_zero a)]
    exact Complex.one_mem_slitPlane
  have hinv : ContinuousOn (fun w : ℕ → ℂ => (fun k => expJetInv a w k)) V := by
    rw [continuousOn_pi]
    exact fun k => continuousOn_expJetInv a k
  have hbase : (fun k => expJetInv a (fun j => expJetScalar y j) k) = y := by
    funext k
    exact expJetInv_expJetScalar y k
  have hpre : ∃ W, IsOpen W ∧ (fun k => expJetScalar y k) ∈ W ∧ W ⊆ V ∧
      ∀ w ∈ W, (fun k => expJetInv a w k) ∈ N := by
    have hmem : (fun w : ℕ → ℂ => (fun k => expJetInv a w k)) ⁻¹' N ∈ nhdsWithin
        (fun k => expJetScalar y k) V := by
      refine hinv _ hΦy ?_
      have hred : ((fun w : ℕ → ℂ => fun k => expJetInv a w k) fun k => expJetScalar y k) = y :=
        hbase
      rw [hred]
      exact hN
    obtain ⟨W₀, hW₀open, hW₀mem, hW₀sub⟩ := mem_nhdsWithin.mp hmem
    exact ⟨W₀ ∩ V, hW₀open.inter hVopen, ⟨hW₀mem, hΦy⟩, Set.inter_subset_right,
      fun w hw => hW₀sub ⟨hw.1, hw.2⟩⟩
  obtain ⟨W, hWopen, hWmem, hWV, hWN⟩ := hpre
  refine Filter.mem_of_superset (hWopen.mem_nhds hWmem) ?_
  intro w hw
  have hw0 : w 0 ≠ 0 := by
    have hmem := hWV hw
    have : w 0 / Complex.exp a ≠ 0 := Complex.slitPlane_ne_zero hmem
    intro hzero
    rw [hzero, zero_div] at this
    exact this rfl
  refine ⟨fun k => expJetInv a w k, hWN w hw, ?_⟩
  funext k
  exact expJetScalar_expJetInv hw0 k

end

end GaloisForLFunctions.HTGeometry
