import GaloisForLFunctions.RHTower.ThetaEulerLogCellResidueChannels

/-!
# Complete orthogonal levels of the actual logarithmic-cell clock

The weighted dyadic cell shift is a pure isometry: its j-th range has no
coordinates below 2^j. Translates of its wandering space are mutually
orthogonal and span the completed cell coefficient space. The existing cell
embedding intertwines every level with the literal iterated translation.
-/

noncomputable section

open RHTower GaloisForLFunctions.HTGeometry.PNatBlock

namespace GaloisForLFunctions.SignedArithmeticHodgeTheory

local notation "CellH" => lp (fun _ : ℕ+ => ℂ) 2
local notation "W" => logCellShift 2

/-- The actual weighted dyadic cell clock, with its proved isometric norm. -/
def logCellDyadicIsometry : CellH →ₗᵢ[ℂ] CellH where
  toLinearMap := (logCellShift 2).toLinearMap
  norm_map' := norm_logCellShift_apply (by norm_num)

/-- Directions perpendicular to every translated cell source. -/
def logCellDyadicWandering : Submodule ℂ CellH :=
  (LinearMap.range (logCellShift 2).toLinearMap)ᗮ

private theorem dyadic_pow_succ (j : ℕ) (x : CellH) :
    (W ^ (j + 1)) x = W ((W ^ j) x) := by
  rw [pow_succ', mul_apply_eq_comp]

private theorem dyadic_pow_add (j k : ℕ) (x : CellH) :
    (W ^ (j + k)) x = (W ^ j) ((W ^ k) x) := by
  rw [pow_add, mul_apply_eq_comp]

private theorem inner_dyadic (x y : CellH) :
    inner ℂ (W x) (W y) = inner ℂ x y :=
  LinearIsometry.inner_map_map logCellDyadicIsometry x y

/-- Every level retains the complete coefficient-space inner product. -/
theorem inner_logCellDyadic_pow (j : ℕ) (x y : CellH) :
    inner ℂ ((W ^ j) x) ((W ^ j) y) = inner ℂ x y := by
  induction j with
  | zero => simp
  | succ j ih => rw [dyadic_pow_succ, dyadic_pow_succ, inner_dyadic, ih]

/-- The j-th translated range starts at integer coordinate 2^j. -/
theorem logCellDyadic_pow_apply_eq_zero (j : ℕ) (x : CellH) (m : ℕ+)
    (hm : (m : ℕ) < 2 ^ j) : ((W ^ j) x) m = 0 := by
  have hW (f : CellH) (n : ℕ+) : (W f) n =
      logCellWeight 2 n * extZero f ((n : ℕ) / 2) :=
    divBlockOp_apply (by norm_num) (norm_logCellWeight_le_one (by norm_num)) f n
  induction j generalizing m with
  | zero => have := m.pos; simp only [pow_zero] at hm; omega
  | succ j ih =>
    rw [dyadic_pow_succ, hW]
    have hdiv : (m : ℕ) / 2 < 2 ^ j := by
      apply (Nat.div_lt_iff_lt_mul (by norm_num)).mpr
      simpa only [pow_succ] using hm
    unfold extZero
    split_ifs with hpos
    · rw [ih ⟨(m : ℕ) / 2, hpos⟩ hdiv, mul_zero]
    · rw [mul_zero]

/-- There is no source component surviving every backward dyadic scale. -/
theorem eq_zero_of_mem_every_logCellDyadic_range {x : CellH}
    (hx : ∀ j : ℕ, ∃ y : CellH, x = (W ^ j) y) : x = 0 := by
  refine lp.ext (funext fun m => ?_)
  obtain ⟨y, hy⟩ := hx (m : ℕ)
  rw [hy, logCellDyadic_pow_apply_eq_zero _ _ m Nat.lt_two_pow_self]
  rfl

private theorem isClosed_dyadic_range :
    IsClosed (LinearMap.range (logCellShift 2).toLinearMap : Set CellH) :=
  (AddMonoidHomClass.isometry_of_norm W
    (norm_logCellShift_apply (by norm_num))).isClosedEmbedding.isClosed_range

private theorem wandering_orthogonal_eq_range :
    logCellDyadicWanderingᗮ = LinearMap.range (logCellShift 2).toLinearMap := by
  haveI : CompleteSpace (LinearMap.range (logCellShift 2).toLinearMap) :=
    isClosed_dyadic_range.completeSpace_coe
  haveI := Submodule.HasOrthogonalProjection.ofCompleteSpace (LinearMap.range (logCellShift 2).toLinearMap)
  exact Submodule.orthogonal_orthogonal _

/-- Different levels of the wandering space are exactly orthogonal. -/
theorem inner_logCellDyadic_wandering {u v : CellH}
    (hu : u ∈ logCellDyadicWandering) (hv : v ∈ logCellDyadicWandering)
    (j k : ℕ) :
    inner ℂ ((W ^ j) u) ((W ^ k) v) = if j = k then inner ℂ u v else 0 := by
  rcases lt_trichotomy j k with hjk | rfl | hkj
  · rw [if_neg hjk.ne]
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_lt hjk
    rw [show j + r + 1 = j + (r + 1) by omega,
      dyadic_pow_add, inner_logCellDyadic_pow, dyadic_pow_succ]
    exact Submodule.inner_left_of_mem_orthogonal
      (LinearMap.mem_range.mpr ⟨_, rfl⟩) hu
  · rw [if_pos rfl, inner_logCellDyadic_pow]
  · rw [if_neg hkj.ne']
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_lt hkj
    rw [show k + r + 1 = k + (r + 1) by omega,
      dyadic_pow_add, inner_logCellDyadic_pow, dyadic_pow_succ]
    exact Submodule.inner_right_of_mem_orthogonal
      (LinearMap.mem_range.mpr ⟨_, rfl⟩) hv

/-- Orthogonality to every wandering level forces a source vector to vanish. -/
theorem eq_zero_of_inner_logCellDyadic_wandering {x : CellH}
    (hx : ∀ j : ℕ, ∀ w ∈ logCellDyadicWandering, inner ℂ ((W ^ j) w) x = 0) :
    x = 0 := by
  have key : ∀ n : ℕ, ∃ y : CellH, x = (W ^ n) y ∧
      ∀ j : ℕ, ∀ w ∈ logCellDyadicWandering, inner ℂ ((W ^ j) w) y = 0 := by
    intro n
    induction n with
    | zero => exact ⟨x, by simp, hx⟩
    | succ n ih =>
      obtain ⟨y, hxy, hy⟩ := ih
      have hyo : y ∈ logCellDyadicWanderingᗮ :=
        (Submodule.mem_orthogonal _ _).mpr fun w hw => by simpa using hy 0 w hw
      rw [wandering_orthogonal_eq_range] at hyo
      obtain ⟨z, hz⟩ := LinearMap.mem_range.mp hyo
      change W z = y at hz
      refine ⟨z, ?_, fun j w hw => ?_⟩
      · rw [hxy, ← hz, pow_succ, mul_apply_eq_comp]
      · have h := hy (j + 1) w hw
        rw [← hz, dyadic_pow_succ, inner_dyadic] at h
        exact h
  exact eq_zero_of_mem_every_logCellDyadic_range fun n => by
    obtain ⟨y, hy, _⟩ := key n
    exact ⟨y, hy⟩

/-- All levels of the actual dyadic wandering space. -/
def logCellDyadicOrbitSet : Set CellH :=
  {x | ∃ j : ℕ, ∃ w ∈ logCellDyadicWandering, x = (W ^ j) w}

/-- Orthogonal dyadic levels exhaust the completed logarithmic-cell space. -/
theorem logCellDyadic_wandering_complete :
    (Submodule.span ℂ logCellDyadicOrbitSet).topologicalClosure = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff]
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  apply eq_zero_of_inner_logCellDyadic_wandering
  intro j w hw
  exact (Submodule.mem_orthogonal _ _).mp hx _
    (Submodule.subset_span ⟨j, w, hw, rfl⟩)

/-- Completion retains the arithmetic source: each clock level is carried to
the same number of literal logarithmic translations. -/
theorem logCellEmbedding_dyadic_pow (j : ℕ) (x : CellH) :
    logCellEmbedding ((W ^ j) x) =
      ((halfLineRightShift (Real.log 2)) ^ j) (logCellEmbedding x) := by
  have hstep (y : CellH) : logCellEmbedding (W y) =
      halfLineRightShift (Real.log 2) (logCellEmbedding y) := by
    simpa only [ContinuousLinearMap.comp_apply, Nat.cast_ofNat] using
      (congrArg (fun T => T y)
        (halfLineRightShift_comp_logCellEmbedding (p := 2) (by norm_num))).symm
  induction j with
  | zero => simp
  | succ j ih =>
    rw [dyadic_pow_succ, hstep, ih, pow_succ', mul_apply_eq_comp]

end GaloisForLFunctions.SignedArithmeticHodgeTheory

#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.eq_zero_of_mem_every_logCellDyadic_range
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.inner_logCellDyadic_wandering
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.logCellDyadic_wandering_complete
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.logCellEmbedding_dyadic_pow
