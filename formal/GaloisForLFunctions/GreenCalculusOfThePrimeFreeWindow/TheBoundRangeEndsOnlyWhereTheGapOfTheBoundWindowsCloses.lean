import GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow.AThinEndIsLogarithmicallyStiffAndAFloorExtendsTheBoundRange
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheRiemannHypothesisIsOneNegativeSquareOfTheNeutralPartOfEveryWindow

/-!
# The bound range ends only where the gap of the bound windows closes

The gap of a window is a lower bound `c` for its neutral form on a hyperplane: its second
eigenvalue is at least `c`. A window `(R, R + J]` with `R ≤ J` and a nonnegative gap holds
exactly one bound state.

* **The gap is the margin** (`hasGap_neutralWindow_iff`): `(R, R + J]` has gap `c` iff `N − c`
  has at most one negative square; the hyperplane can be taken orthogonal to the ground vector.
* **The gap decreases with the window** (`hasGap_neutralWindow_of_hasGap_add`) **and along the
  refinement tower** (`hasGap_neutralWindow_of_hasGap_refined`), **and is lower semicontinuous**
  (`hasGap_neutralWindow_of_thin_tail`): a gap `c` of `(R, R + J]` gives the gap `c − ε` of
  `(R, R + J + j]` when `K j ≤ R + J` and `log K ≥ c − ε + B²/ε + 2`,
  `B = 24 + 2 Σ_{k ≤ Q} Λ(k)`. So the bound range is open, and a thin step adds at most `ε` to
  the margin at every level (`hermNegIndex_neutralWindow_add_diagonal_le_one_of_thin_tail`).
  Through the tower the certified range is exceeded at every block size
  (`hasGap_neutralWindow_beyond_certified`).
* **The continuity method** (`hermNegIndex_neutralWindow_eq_one_of_gap`): fix the cutoff `Q` and
  a bound `a/b` for the ratio `(R + J)/R`. If the windows of ratio at most `a/b` that hold
  exactly one bound state have a common gap `c > 0`, then every window of ratio at most `a/b`
  holds exactly one bound state. The proof starts in the certified range at block size `K R`,
  adds one block at a time, a thin end at that block size, and returns to block size `R` along
  the refinement tower.
* **The gap closes before an unbound window** (`exists_bound_window_without_gap`): if
  `(R, R + J]` does not hold exactly one bound state, then for every `c > 0` some window of at
  most the same ratio holds exactly one bound state and has no gap `c`.
* **The Riemann hypothesis from an a priori gap** (`riemannHypothesis_of_gap_of_bound_windows`):
  if at every cutoff the windows that hold exactly one bound state have a common positive gap,
  the Riemann hypothesis holds. The estimate is asked only of windows that are already bound.
-/

open Finset Matrix
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.AbsoluteGeometryOfSpecZ
open GaloisForLFunctions.MixingArithmeticOfTheFloorTrees

noncomputable section

namespace GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow

/-! ### The gap of a form -/

section Gap

variable {ι : Type*} [Fintype ι]

/-- The form of `M` has gap `c`: it is at least `c` on a hyperplane, so the second eigenvalue of
`M` is at least `c`. -/
def HasGap (M : Matrix ι ι ℝ) (c : ℝ) : Prop :=
  ∃ ℓ : ι → ℝ, ∀ y : ι → ℝ, ℓ ⬝ᵥ y = 0 → c * (y ⬝ᵥ y) ≤ y ⬝ᵥ (M *ᵥ y)

/-- The floor of one bound state is a gap. -/
theorem OneBoundState.hasGap {M : Matrix ι ι ℝ} {φ : ι → ℝ} {μ c : ℝ}
    (h : OneBoundState M φ μ c) : HasGap M c :=
  ⟨φ, h.floor⟩

theorem HasGap.mono {M : Matrix ι ι ℝ} {c c' : ℝ} (h : HasGap M c) (hc : c' ≤ c) :
    HasGap M c' := by
  obtain ⟨ℓ, hℓ⟩ := h
  refine ⟨ℓ, fun y hy => le_trans ?_ (hℓ y hy)⟩
  have hy0 : 0 ≤ y ⬝ᵥ y := dotProduct_self_star_nonneg (v := y)
  exact mul_le_mul_of_nonneg_right hc hy0

/-- A form with a nonnegative gap has at most one negative square. -/
theorem HasGap.hermNegIndex_le_one {M : Matrix ι ι ℝ} {c : ℝ} (hc : 0 ≤ c) (h : HasGap M c) :
    hermNegIndex (M.map (↑) : Matrix ι ι ℂ) ≤ 1 := by
  obtain ⟨ℓ, hℓ⟩ := h
  refine hermNegIndex_le_one_of_nonneg_on_hyperplane M ℓ fun y hy => le_trans ?_ (hℓ y hy)
  have hy0 : 0 ≤ y ⬝ᵥ y := dotProduct_self_star_nonneg (v := y)
  exact mul_nonneg hc hy0

end Gap

/-! ### The gap is the margin -/

section Margin

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A gap `c` is a margin `−c`: `M − c` has at most one negative square. -/
theorem HasGap.hermNegIndex_add_diagonal_le_one {M : Matrix ι ι ℝ} {c : ℝ} (h : HasGap M c) :
    hermNegIndex ((M + Matrix.diagonal fun _ => -c).map (↑) : Matrix ι ι ℂ) ≤ 1 := by
  obtain ⟨ℓ, hℓ⟩ := h
  refine hermNegIndex_le_one_of_nonneg_on_hyperplane _ ℓ fun y hy => ?_
  rw [dotProduct_add_diagonal_mulVec]
  linarith [hℓ y hy]

/-- **A margin is a gap on the complement of the ground vector.** Let `G` be symmetric with
entries `≤ 0` off the diagonal and a positive eigenvector `φ`. If `G − c` has at most one
negative square, then `G ⪰ c` on `φ^⊥`: the Poincaré inequality of the Doob chain of `G − c`. -/
theorem hasGap_of_hermNegIndex_add_diagonal_le_one {G : Matrix ι ι ℝ}
    (hG : ∀ i j, G i j = G j i) (hoff : ∀ i j, i ≠ j → G i j ≤ 0) {φ : ι → ℝ}
    (hφ : ∀ i, 0 < φ i) {lam : ℝ} (heig : G *ᵥ φ = lam • φ) {c : ℝ}
    (h : hermNegIndex ((G + Matrix.diagonal fun _ => -c).map (↑) : Matrix ι ι ℂ) ≤ 1) :
    HasGap G c := by
  refine ⟨φ, fun y hy => ?_⟩
  have hG' := symm_add_diagonal hG (-c)
  have hoff' : ∀ i j, i ≠ j → (G + Matrix.diagonal fun _ => -c : Matrix ι ι ℝ) i j ≤ 0 :=
      fun i j hij => by
    rw [Matrix.add_apply, Matrix.diagonal_apply_ne _ hij, add_zero]
    exact hoff i j hij
  have heig' : (G + Matrix.diagonal fun _ => -c) *ᵥ φ = (lam + -c) • φ := by
    rw [Matrix.add_mulVec, heig, diagonal_const_mulVec, add_smul]
  have hcancel : ∀ i, φ i * (y i / φ i) = y i := fun i => by
    rw [div_eq_mul_inv, mul_left_comm, mul_inv_cancel₀ (hφ i).ne', mul_one]
  have hmean : doobMean φ (fun i => y i / φ i) = 0 := by
    rw [← hy]
    show ∑ i, φ i ^ 2 * (y i / φ i) = ∑ i, φ i * y i
    exact Finset.sum_congr rfl fun i _ => by rw [pow_two, mul_assoc, hcancel]
  have hP := (hermNegIndex_le_one_iff_poincare hG' hoff' hφ heig').mp h _ hmean
  have hb := bilin_mul_eq_doob hG' heig' (fun i => y i / φ i)
  simp only [hcancel] at hb
  rw [← dotProduct_mulVec_eq_bilin, dotProduct_add_diagonal_mulVec] at hb
  linarith

/-- **The gap is the margin**: for a symmetric matrix with entries `≤ 0` off the diagonal and a
positive eigenvector, a gap `c` is the same as at most one negative square of `G − c`. -/
theorem hasGap_iff_hermNegIndex_add_diagonal_le_one {G : Matrix ι ι ℝ}
    (hG : ∀ i j, G i j = G j i) (hoff : ∀ i j, i ≠ j → G i j ≤ 0) {φ : ι → ℝ}
    (hφ : ∀ i, 0 < φ i) {lam : ℝ} (heig : G *ᵥ φ = lam • φ) (c : ℝ) :
    HasGap G c ↔
      hermNegIndex ((G + Matrix.diagonal fun _ => -c).map (↑) : Matrix ι ι ℂ) ≤ 1 :=
  ⟨fun h => h.hermNegIndex_add_diagonal_le_one,
    hasGap_of_hermNegIndex_add_diagonal_le_one hG hoff hφ heig⟩

end Margin

/-! ### The bound range is open -/

/-- A window with `R ≤ J` and a nonnegative gap holds exactly one bound state. -/
theorem hermNegIndex_neutralWindow_eq_one_of_hasGap {Q R J : ℕ} (hR : 1 ≤ R) (hRJ : R ≤ J)
    {c : ℝ} (hc : 0 ≤ c) (h : HasGap (neutralWindow Q R J) c) :
    hermNegIndex ((neutralWindow Q R J).map (↑) : Matrix (Fin J) (Fin J) ℂ) = 1 :=
  le_antisymm (h.hermNegIndex_le_one hc) (one_le_hermNegIndex_neutralWindow Q hR hRJ)

/-- **The bound range is open: the gap is lower semicontinuous in the window.** A gap `c` of
`(R, R + J]` gives the gap `c − ε` of `(R, R + J + j]` when `K j ≤ R + J` and
`log K ≥ c − ε + B²/ε + 2`, `B = 24 + 2 Σ_{k ≤ Q} Λ(k)`, `ε > 0`. -/
theorem hasGap_neutralWindow_of_thin_tail {Q R J j K : ℕ} (hK : 16 ≤ K) (hj : K * j ≤ R + J)
    {c ε : ℝ} (hε : 0 < ε) (h : HasGap (neutralWindow Q R J) c)
    (hs : c - ε + (24 + 2 * primeContactSum Q) ^ 2 / ε + 2 ≤ Real.log K) :
    HasGap (neutralWindow Q R (J + j)) (c - ε) := by
  obtain ⟨ℓ, hℓ⟩ := h
  exact ⟨headFunctional ℓ j, fun y hy => neutralWindow_form_ge_of_thin_tail hK hj hε hℓ hs hy⟩

theorem headPart_headFunctional {J : ℕ} (m : Fin J → ℝ) (j : ℕ) :
    headPart (headFunctional m j) = m := by
  funext i
  simp only [headPart, headFunctional, Function.comp_apply, Equiv.symm_apply_apply,
    Sum.elim_inl]

theorem tailPart_headFunctional {J : ℕ} (m : Fin J → ℝ) (j : ℕ) :
    tailPart (headFunctional m j) = 0 := by
  funext l
  simp only [tailPart, headFunctional, Function.comp_apply, Equiv.symm_apply_apply,
    Sum.elim_inr, Pi.zero_apply]

/-- **The gap decreases with the window**: a gap of `(R, R + J + j]` is a gap of `(R, R + J]`. -/
theorem hasGap_neutralWindow_of_hasGap_add {Q R J j : ℕ} {c : ℝ}
    (h : HasGap (neutralWindow Q R (J + j)) c) : HasGap (neutralWindow Q R J) c := by
  obtain ⟨ℓ, hℓ⟩ := h
  refine ⟨headPart ℓ, fun m hm => ?_⟩
  have h0 : ℓ ⬝ᵥ headFunctional m j = 0 := by
    rw [dotProduct_comm, headFunctional_dotProduct, dotProduct_comm]
    exact hm
  have h1 := hℓ (headFunctional m j) h0
  rw [neutralWindow_form_eq_head_tail, dotProduct_self_eq_head_add_tail,
    headPart_headFunctional, tailPart_headFunctional, dotProduct_fromBlocks_mulVec] at h1
  simp only [Matrix.mulVec_zero, dotProduct_zero, mul_zero, add_zero] at h1
  exact h1

/-- **The gap of a window is its margin**: `(R, R + J]` has gap `c` iff `N − c` has at most
one negative square. -/
theorem hasGap_neutralWindow_iff (Q R : ℕ) {J : ℕ} (hJ : 1 ≤ J) (c : ℝ) :
    HasGap (neutralWindow Q R J) c ↔
      hermNegIndex ((neutralWindow Q R J + Matrix.diagonal fun _ => -c).map (↑) :
        Matrix (Fin J) (Fin J) ℂ) ≤ 1 := by
  obtain ⟨φ, hφ, lam, heig⟩ := exists_groundVector_neutralWindow Q R hJ
  exact hasGap_iff_hermNegIndex_add_diagonal_le_one (neutralWindow_symm Q R J)
    (fun _ _ hij => (neutralWindow_neg_of_ne Q R hij).le) hφ heig c

/-- **The gap decreases along the refinement tower**: a gap of `(mR, mR + mJ]` is a gap of
`(R, R + J]`. -/
theorem hasGap_neutralWindow_of_hasGap_refined {Q R J m : ℕ} (hR : 1 ≤ R) (hm : 1 ≤ m)
    (hJ : 1 ≤ J) {c : ℝ} (h : HasGap (neutralWindow Q (m * R) (m * J)) c) :
    HasGap (neutralWindow Q R J) c :=
  (hasGap_neutralWindow_iff Q R hJ c).mpr
    ((hermNegIndex_neutralWindow_add_le_refined hR hm Q J (-c)).trans
      h.hermNegIndex_add_diagonal_le_one)

/-- **The loss of a thin step.** If `N + C` has at most one negative square on `(R, R + J]` and
`log K ≥ −C − ε + B²/ε + 2`, `B = 24 + 2 Σ_{k ≤ Q} Λ(k)`, `ε > 0`, then `N + C + ε` has at most
one negative square on `(R, R + J + j]`, `K j ≤ R + J`: a thin end of relative width `1/K` adds
at most `ε` to the margin, at every level and every block size. -/
theorem hermNegIndex_neutralWindow_add_diagonal_le_one_of_thin_tail {Q R J j K : ℕ}
    (hJ : 1 ≤ J) (hK : 16 ≤ K) (hj : K * j ≤ R + J) {C ε : ℝ} (hε : 0 < ε)
    (h : hermNegIndex ((neutralWindow Q R J + Matrix.diagonal fun _ => C).map (↑) :
      Matrix (Fin J) (Fin J) ℂ) ≤ 1)
    (hs : -C - ε + (24 + 2 * primeContactSum Q) ^ 2 / ε + 2 ≤ Real.log K) :
    hermNegIndex ((neutralWindow Q R (J + j) + Matrix.diagonal fun _ => C + ε).map (↑) :
      Matrix (Fin (J + j)) (Fin (J + j)) ℂ) ≤ 1 := by
  have hg : HasGap (neutralWindow Q R J) (-C) :=
    (hasGap_neutralWindow_iff Q R hJ (-C)).mpr (by rwa [neg_neg])
  have h' := (hasGap_neutralWindow_of_thin_tail hK hj hε hg hs).hermNegIndex_add_diagonal_le_one
  rwa [show -(-C - ε) = C + ε by ring] at h'

/-- **Beyond the certified range at every block size.** For `log K ≥ 6760003`, every window
`(R, R + J]` with `R ≤ J` and `50 K J ≤ (53 K + 103) R` has gap `1/10000`: the ratio may exceed
`103/50` by its fraction `1/K`. The window is refined to block size `50 R`, where it is the
certified window `(50 R, 103 R]` and a thin end. -/
theorem hasGap_neutralWindow_beyond_certified {Q R J K : ℕ} (hQ : 2 ≤ Q) (hR : 1 ≤ R)
    (hRJ : R ≤ J) (hK : (6760003 : ℝ) ≤ Real.log K) (hJ : 50 * K * J ≤ (53 * K + 103) * R) :
    HasGap (neutralWindow Q R J) (1 / 10000) := by
  by_cases hcert : 50 * J ≤ 53 * R
  · obtain ⟨ψ, ν, -, h⟩ := exists_oneBoundState_neutralWindow hR hRJ hcert hQ
    exact h.hasGap.mono (by norm_num)
  · obtain ⟨d, hd⟩ : ∃ d, 50 * J = 53 * R + d := ⟨50 * J - 53 * R, by omega⟩
    have h1 : K * (53 * R + d) ≤ (53 * K + 103) * R := by
      rw [← hd]
      calc K * (50 * J) = 50 * K * J := by ring
        _ ≤ (53 * K + 103) * R := hJ
    have h2 : K * (53 * R + d) = 53 * K * R + K * d := by ring
    have h3 : (53 * K + 103) * R = 53 * K * R + 103 * R := by ring
    have hj : K * d ≤ 50 * R + 53 * R := by omega
    obtain ⟨ψ', ν', -, h⟩ := exists_oneBoundState_neutralWindow_beyond_certified
      (J := 53 * R) (j := d) hQ (by omega : 1 ≤ 50 * R) (by omega : 50 * R ≤ 53 * R)
      (by omega) hK hj
    have hg := h.hasGap
    rw [← hd] at hg
    exact hasGap_neutralWindow_of_hasGap_refined hR (by norm_num : 1 ≤ 50) (by omega) hg

/-- Every real number is below the logarithm of a natural number `K ≥ 16`. -/
theorem exists_sixteen_le_and_le_log (x : ℝ) : ∃ K : ℕ, 16 ≤ K ∧ x ≤ Real.log K := by
  refine ⟨max 16 ⌈Real.exp x⌉₊, le_max_left _ _, ?_⟩
  have h1 : Real.exp x ≤ ((max 16 ⌈Real.exp x⌉₊ : ℕ) : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right _ _))
  calc x = Real.log (Real.exp x) := (Real.log_exp x).symm
    _ ≤ Real.log ((max 16 ⌈Real.exp x⌉₊ : ℕ) : ℝ) := Real.log_le_log (Real.exp_pos x) h1

/-! ### The continuity method -/

/-- **The continuity method.** Fix the cutoff `Q ≥ 2` and a bound `a/b` for the ratio. If the
windows of ratio at most `a/b` that hold exactly one bound state have a common gap `c > 0`, then
every window of ratio at most `a/b` holds exactly one bound state.

At block size `K R`, `log K ≥ c/2 + 2B²/c + 2`, one block is a thin end of every window: from the
certified window `(K R, 2 K R]` the windows `(K R, K R + J']` are bound one block after the
other, each by the gap of the one before, up to `J' = K J`. The window `(R, R + J]` has at most
as many bound states as its refinement `(K R, K R + K J]`. -/
theorem hermNegIndex_neutralWindow_eq_one_of_gap {Q a b : ℕ} (hQ : 2 ≤ Q) {c : ℝ} (hc : 0 < c)
    (hgap : ∀ R J : ℕ, 1 ≤ R → R ≤ J → b * (R + J) ≤ a * R →
      hermNegIndex ((neutralWindow Q R J).map (↑) : Matrix (Fin J) (Fin J) ℂ) = 1 →
        HasGap (neutralWindow Q R J) c)
    {R J : ℕ} (hR : 1 ≤ R) (hRJ : R ≤ J) (hab : b * (R + J) ≤ a * R) :
    hermNegIndex ((neutralWindow Q R J).map (↑) : Matrix (Fin J) (Fin J) ℂ) = 1 := by
  obtain ⟨K, hK16, hs⟩ := exists_sixteen_le_and_le_log
    (c - c / 2 + (24 + 2 * primeContactSum Q) ^ 2 / (c / 2) + 2)
  have hKle : K ≤ K * R := Nat.le_mul_of_pos_right K (by omega)
  have hKR1 : 1 ≤ K * R := by omega
  -- the refinement stays below the ratio `a/b`
  have hcap : ∀ n : ℕ, n ≤ K * J → b * (K * R + n) ≤ a * (K * R) := fun n hn =>
    calc b * (K * R + n) ≤ b * (K * R + K * J) := Nat.mul_le_mul_left b (by omega)
      _ = K * (b * (R + J)) := by ring
      _ ≤ K * (a * R) := Nat.mul_le_mul_left K hab
      _ = a * (K * R) := by ring
  -- one block at a time at block size `K R`
  have key : ∀ J' : ℕ, K * R ≤ J' → J' ≤ K * J →
      hermNegIndex ((neutralWindow Q (K * R) J').map (↑) : Matrix (Fin J') (Fin J') ℂ) = 1 := by
    intro J' hJ'
    refine Nat.le_induction (fun _ => ?_) (fun n hn ih hle => ?_) J' hJ'
    · obtain ⟨ψ, ν, -, h⟩ := exists_oneBoundState_neutralWindow hKR1 le_rfl (by omega) hQ
      exact h.hermNegIndex_eq_one
    · have h1 := ih (by omega)
      have hg := hgap (K * R) n hKR1 hn (hcap n (by omega)) h1
      have hg' := hasGap_neutralWindow_of_thin_tail (j := 1) hK16 (by omega) (half_pos hc) hg hs
      exact hermNegIndex_neutralWindow_eq_one_of_hasGap hKR1 (by omega) (by linarith) hg'
  have hfine := key (K * J) (Nat.mul_le_mul_left K hRJ) le_rfl
  have hle := hermNegIndex_neutralWindow_le_refined hR (by omega : 1 ≤ K) Q J
  rw [hfine] at hle
  exact le_antisymm hle (one_le_hermNegIndex_neutralWindow Q hR hRJ)

/-- **The gap closes before an unbound window.** If `(R, R + J]`, `R ≤ J`, does not hold exactly
one bound state, then for every `c > 0` some window `(R', R' + J']` with `J'/R' ≤ J/R` holds
exactly one bound state and has no gap `c`. -/
theorem exists_bound_window_without_gap {Q R J : ℕ} (hQ : 2 ≤ Q) (hR : 1 ≤ R) (hRJ : R ≤ J)
    (hne : hermNegIndex ((neutralWindow Q R J).map (↑) : Matrix (Fin J) (Fin J) ℂ) ≠ 1)
    {c : ℝ} (hc : 0 < c) :
    ∃ R' J' : ℕ, 1 ≤ R' ∧ R' ≤ J' ∧ J' * R ≤ J * R' ∧
      hermNegIndex ((neutralWindow Q R' J').map (↑) : Matrix (Fin J') (Fin J') ℂ) = 1 ∧
        ¬ HasGap (neutralWindow Q R' J') c := by
  by_contra hno
  refine hne (hermNegIndex_neutralWindow_eq_one_of_gap (a := R + J) (b := R) hQ hc
    (fun R' J' h1 h2 h3 h4 => ?_) hR hRJ (Nat.mul_comm _ _).le)
  by_contra hg
  refine hno ⟨R', J', h1, h2, ?_, h4, hg⟩
  have h5 : R * R' + J' * R ≤ R * R' + J * R' := by
    calc R * R' + J' * R = R * (R' + J') := by ring
      _ ≤ (R + J) * R' := h3
      _ = R * R' + J * R' := by ring
  omega

/-- **The Riemann hypothesis from an a priori gap.** If at every cutoff `Q` the windows
`(R, R + J]` with `R ≤ J`, `R + J ≤ Q R` that hold exactly one bound state have a common
positive gap, the Riemann hypothesis holds. -/
theorem riemannHypothesis_of_gap_of_bound_windows
    (h : ∀ Q : ℕ, 2 ≤ Q → ∃ c : ℝ, 0 < c ∧ ∀ R J : ℕ, 1 ≤ R → R ≤ J → R + J ≤ Q * R →
      hermNegIndex ((neutralWindow Q R J).map (↑) : Matrix (Fin J) (Fin J) ℂ) = 1 →
        HasGap (neutralWindow Q R J) c) : RiemannHypothesis := by
  rw [riemannHypothesis_iff_forall_hermNegIndex_neutralWindow_eq_one]
  intro Q R J hR hRJ hQ
  have hQ2 : 2 ≤ Q := by
    by_contra hlt
    have h1 : Q * R ≤ 1 * R := Nat.mul_le_mul_right R (by omega)
    omega
  obtain ⟨c, hc, hgap⟩ := h Q hQ2
  exact hermNegIndex_neutralWindow_eq_one_of_gap (a := Q) (b := 1) hQ2 hc
    (fun R' J' h1 h2 h3 => hgap R' J' h1 h2 (by omega)) hR hRJ (by omega)

end GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow
