import GaloisForLFunctions.RHTower.MobiusPrimeRenewalDefectBoundary
import Mathlib.Combinatorics.Hall.Basic

/-!
# Opposite-sign transport consumer for the Möbius boundary

A local pairing of positive and negative boundary atoms converts into a Laplace bound through a
sharp damped displacement cost.  This module formalizes the unconditional analytic implication
used by the `FOUR-PRIME-BOUNDARY-TRANSPORT` conjecture; it does not assume that the arithmetic
matching exists.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

private theorem abs_exp_neg_mul_sub_exp_neg_mul_le_of_le
    {u v x : ℝ} (huv : u ≤ v) (hx : 0 ≤ x) :
    |Real.exp (-(u * x)) - Real.exp (-(v * x))| ≤
      x * |u - v| * Real.exp (-(min u v * x)) := by
  have horder : Real.exp (-(v * x)) ≤ Real.exp (-(u * x)) := by
    rw [Real.exp_le_exp]
    exact neg_le_neg (mul_le_mul_of_nonneg_right huv hx)
  rw [abs_of_nonneg (sub_nonneg.mpr horder), min_eq_left huv,
    abs_of_nonpos (sub_nonpos.mpr huv)]
  have hfactor :
      Real.exp (-(u * x)) - Real.exp (-(v * x)) =
        Real.exp (-(u * x)) * (1 - Real.exp (-((v - u) * x))) := by
    rw [mul_sub, mul_one, ← Real.exp_add]
    congr 1
    ring_nf
  rw [hfactor]
  have hdefect : 1 - Real.exp (-((v - u) * x)) ≤ (v - u) * x := by
    have h := Real.add_one_le_exp (-((v - u) * x))
    linarith
  calc
    Real.exp (-(u * x)) * (1 - Real.exp (-((v - u) * x))) ≤
        Real.exp (-(u * x)) * ((v - u) * x) :=
      mul_le_mul_of_nonneg_left hdefect (Real.exp_pos _).le
    _ = x * -(u - v) * Real.exp (-(u * x)) := by ring_nf

/-- Sharp one-edge transport estimate for the positive exponential kernel. -/
theorem abs_exp_neg_mul_sub_exp_neg_mul_le_transportCost
    {u v x : ℝ} (hx : 0 ≤ x) :
    |Real.exp (-(u * x)) - Real.exp (-(v * x))| ≤
      x * |u - v| * Real.exp (-(min u v * x)) := by
  by_cases huv : u ≤ v
  · exact abs_exp_neg_mul_sub_exp_neg_mul_le_of_le huv hx
  · have hvu : v ≤ u := le_of_not_ge huv
    simpa [abs_sub_comm, min_comm] using
      (abs_exp_neg_mul_sub_exp_neg_mul_le_of_le hvu hx)

/-- Aggregate damped displacement cost of a finite family of opposite-sign pairs. -/
def finiteDampedLaplaceTransportCost
    {ι : Type*} (s : Finset ι) (u v : ι → ℝ) (x : ℝ) : ℝ :=
  ∑ i ∈ s,
    x * |u i - v i| * Real.exp (-(min (u i) (v i) * x))

/-- Exact transport consumer: paired opposite-sign atoms cost only damped displacement; all
unpaired or truncated atoms may be placed in the explicit remainder `r`. -/
theorem abs_sum_exp_neg_mul_sub_exp_neg_mul_add_le_transportCost
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (u v : ι → ℝ)
    {x : ℝ} (hx : 0 ≤ x) (r : ℝ) :
    |(∑ i ∈ s, (Real.exp (-(u i * x)) - Real.exp (-(v i * x)))) + r| ≤
      finiteDampedLaplaceTransportCost s u v x + |r| := by
  calc
    |(∑ i ∈ s, (Real.exp (-(u i * x)) - Real.exp (-(v i * x)))) + r| ≤
        |∑ i ∈ s, (Real.exp (-(u i * x)) - Real.exp (-(v i * x)))| + |r| :=
      abs_add_le _ _
    _ ≤ (∑ i ∈ s,
          |Real.exp (-(u i * x)) - Real.exp (-(v i * x))|) + |r| :=
      add_le_add (Finset.abs_sum_le_sum_abs _ _) (le_refl _)
    _ ≤ finiteDampedLaplaceTransportCost s u v x + |r| := by
      exact add_le_add
        (Finset.sum_le_sum fun i _hi =>
          abs_exp_neg_mul_sub_exp_neg_mul_le_transportCost hx)
        (le_refl _)

/-- Hall selection plus a pointwise edge envelope gives a globally injective transport whose
cost obeys the same envelope on every finite subfamily.  This keeps the arithmetic burden exact:
one must prove the Hall inequalities for the proposed boundary graph and the stated cost bound on
every admissible edge. -/
theorem exists_injective_dampedLaplaceTransport_of_hall
    {ι α : Type*} [DecidableEq α] (t : ι → Finset α)
    (u : ι → ℝ) (v : α → ℝ) (bound : ι → ℝ) (x : ℝ)
    (hHall : ∀ s : Finset ι, s.card ≤ (s.biUnion t).card)
    (hEdge : ∀ i a, a ∈ t i →
      x * |u i - v a| * Real.exp (-(min (u i) (v a) * x)) ≤ bound i) :
    ∃ f : ι → α,
      Function.Injective f ∧
      (∀ i, f i ∈ t i) ∧
      ∀ s : Finset ι,
        finiteDampedLaplaceTransportCost s u (v ∘ f) x ≤ ∑ i ∈ s, bound i := by
  obtain ⟨f, hf_injective, hf_mem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp hHall
  refine ⟨f, hf_injective, hf_mem, ?_⟩
  intro s
  exact Finset.sum_le_sum fun i _hi => hEdge i (f i) (hf_mem i)

/-- A symmetric conductance supported on sign-reversing edges has zero signed row mass.  This is
the algebraic core of fractional opposite-sign transport. -/
theorem parityFlippingConductance_rowSum_eq_zero
    {ι : Type*} [Fintype ι] (sign : ι → ℝ) (c : ι → ι → ℝ)
    (hsymm : ∀ i j, c i j = c j i)
    (hflip : ∀ i j, c i j ≠ 0 → sign i + sign j = 0) :
    ∑ i, sign i * ∑ j, c i j = 0 := by
  classical
  let S : ℝ := ∑ i, sign i * ∑ j, c i j
  have hswap : (∑ i, ∑ j, sign j * c i j) = S := by
    calc
      (∑ i, ∑ j, sign j * c i j) = ∑ j, ∑ i, sign j * c i j :=
        Finset.sum_comm
      _ = ∑ j, ∑ i, sign j * c j i := by
        apply Finset.sum_congr rfl
        intro j _hj
        apply Finset.sum_congr rfl
        intro i _hi
        rw [hsymm i j]
      _ = S := by simp [S, Finset.mul_sum]
  have hpair : ∀ i j, (sign i + sign j) * c i j = 0 := by
    intro i j
    by_cases hc : c i j = 0
    · simp [hc]
    · rw [hflip i j hc, zero_mul]
  have hdouble : S + S = 0 := by
    calc
      S + S =
          (∑ i, ∑ j, sign i * c i j) +
            (∑ i, ∑ j, sign j * c i j) := by
        rw [hswap]
        simp [S, Finset.mul_sum]
      _ = ∑ i, ∑ j, (sign i + sign j) * c i j := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _hi
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _hj
        ring
      _ = 0 := by simp [hpair]
  linarith

/-- Exact fractional-transport consumer.  If a symmetric parity-flipping conductance uses at most
the available weight at each vertex, then total unused capacity bounds the signed mass. -/
theorem abs_sum_sign_weight_le_unusedConductance
    {ι : Type*} [Fintype ι] (sign weight : ι → ℝ) (c : ι → ι → ℝ)
    (hsign : ∀ i, |sign i| = 1)
    (hsymm : ∀ i j, c i j = c j i)
    (hflip : ∀ i j, c i j ≠ 0 → sign i + sign j = 0)
    (hcapacity : ∀ i, ∑ j, c i j ≤ weight i) :
    |∑ i, sign i * weight i| ≤ ∑ i, (weight i - ∑ j, c i j) := by
  classical
  have hcancel := parityFlippingConductance_rowSum_eq_zero sign c hsymm hflip
  have hrewrite :
      (∑ i, sign i * weight i) =
        ∑ i, sign i * (weight i - ∑ j, c i j) := by
    calc
      (∑ i, sign i * weight i) =
          (∑ i, sign i * weight i) - ∑ i, sign i * ∑ j, c i j := by
        rw [hcancel, sub_zero]
      _ = ∑ i, (sign i * weight i - sign i * ∑ j, c i j) := by
        rw [Finset.sum_sub_distrib]
      _ = ∑ i, sign i * (weight i - ∑ j, c i j) := by
        apply Finset.sum_congr rfl
        intro i _hi
        ring
  rw [hrewrite]
  calc
    |∑ i, sign i * (weight i - ∑ j, c i j)| ≤
        ∑ i, |sign i * (weight i - ∑ j, c i j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, (weight i - ∑ j, c i j) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [abs_mul, hsign i, one_mul, abs_of_nonneg]
      exact sub_nonneg.mpr (hcapacity i)

/-- Neighbor set of a finite arithmetic replacement relation. -/
def finiteReplacementNeighbors
    {ι : Type*} [Fintype ι] (adj : ι → ι → Prop) [DecidableRel adj] (i : ι) : Finset ι :=
  Finset.univ.filter (adj i)

/-- Canonical symmetric conductance obtained by taking the smaller normalized endpoint weight on
each replacement edge. -/
def symmetricMinConductance
    {ι : Type*} (adj : ι → ι → Prop) [DecidableRel adj] (a : ι → ℝ) (i j : ι) : ℝ :=
  if adj i j then min (a i) (a j) else 0

theorem symmetricMinConductance_symm
    {ι : Type*} (adj : ι → ι → Prop) [DecidableRel adj] (a : ι → ℝ)
    (hadj_symm : ∀ {i j}, adj i j → adj j i) (i j : ι) :
    symmetricMinConductance adj a i j = symmetricMinConductance adj a j i := by
  by_cases hij : adj i j
  · rw [symmetricMinConductance, if_pos hij,
      symmetricMinConductance, if_pos (hadj_symm hij), min_comm]
  · have hji : ¬adj j i := fun h => hij (hadj_symm h)
    rw [symmetricMinConductance, if_neg hij,
      symmetricMinConductance, if_neg hji]

theorem sum_symmetricMinConductance_eq_sum_neighbors
    {ι : Type*} [Fintype ι] (adj : ι → ι → Prop) [DecidableRel adj]
    (a : ι → ℝ) (i : ι) :
    ∑ j, symmetricMinConductance adj a i j =
      ∑ j ∈ finiteReplacementNeighbors adj i, min (a i) (a j) := by
  rw [finiteReplacementNeighbors, Finset.sum_filter]
  rfl

/-- Canonical fractional-flow reduction.  `residual` accounts for isolated or deliberately
discarded capacity; normalized endpoint weights `a` account for all remaining capacity.  The
signed mass is bounded by residual capacity plus directed normalized-weight variation on explicit
parity-flipping replacement edges. -/
theorem abs_sum_sign_weight_le_symmetricMinConductanceDefect
    {ι : Type*} [Fintype ι] (adj : ι → ι → Prop) [DecidableRel adj]
    (sign weight residual a : ι → ℝ)
    (hsign : ∀ i, |sign i| = 1)
    (hadj_symm : ∀ {i j}, adj i j → adj j i)
    (hadj_flip : ∀ {i j}, adj i j → sign i + sign j = 0)
    (hresidual : ∀ i, 0 ≤ residual i)
    (hnormalize : ∀ i,
      weight i = residual i + ∑ _j ∈ finiteReplacementNeighbors adj i, a i) :
    |∑ i, sign i * weight i| ≤
      (∑ i, residual i) +
        ∑ i, ∑ j ∈ finiteReplacementNeighbors adj i,
          (a i - min (a i) (a j)) := by
  classical
  let c : ι → ι → ℝ := symmetricMinConductance adj a
  have hc_symm : ∀ i j, c i j = c j i := by
    intro i j
    exact symmetricMinConductance_symm adj a hadj_symm i j
  have hc_flip : ∀ i j, c i j ≠ 0 → sign i + sign j = 0 := by
    intro i j hc
    apply hadj_flip
    by_contra hij
    exact hc (by simp [c, symmetricMinConductance, hij])
  have hc_capacity : ∀ i, ∑ j, c i j ≤ weight i := by
    intro i
    rw [show (∑ j, c i j) =
      ∑ j ∈ finiteReplacementNeighbors adj i, min (a i) (a j) by
        exact sum_symmetricMinConductance_eq_sum_neighbors adj a i]
    calc
      (∑ j ∈ finiteReplacementNeighbors adj i, min (a i) (a j)) ≤
          ∑ j ∈ finiteReplacementNeighbors adj i, a i :=
        Finset.sum_le_sum fun _j _hj => min_le_left _ _
      _ ≤ weight i := by rw [hnormalize i]; linarith [hresidual i]
  have hconsumer :=
    abs_sum_sign_weight_le_unusedConductance sign weight c hsign hc_symm hc_flip hc_capacity
  calc
    |∑ i, sign i * weight i| ≤ ∑ i, (weight i - ∑ j, c i j) := hconsumer
    _ = ∑ i, (residual i +
          ∑ j ∈ finiteReplacementNeighbors adj i, (a i - min (a i) (a j))) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [hnormalize i,
        show (∑ j, c i j) =
          ∑ j ∈ finiteReplacementNeighbors adj i, min (a i) (a j) by
            exact sum_symmetricMinConductance_eq_sum_neighbors adj a i]
      rw [Finset.sum_sub_distrib]
      ring
    _ = (∑ i, residual i) +
          ∑ i, ∑ j ∈ finiteReplacementNeighbors adj i,
            (a i - min (a i) (a j)) := by
      rw [Finset.sum_add_distrib]

end

end RHTower
