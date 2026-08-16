import GaloisForLFunctions.HTGeometry.DefectSlopeNormalForm

/-!
# The spectral phase bandwidth of a centralizer element

A phase assignment on an ordered spectrum has a bandwidth: the least Lipschitz constant of a real
function through the prescribed phases, read modulo `2π`.  The bandwidth is a nearest-neighbour
quantity,

`bw = maxⱼ circDist(θⱼ₊₁, θⱼ) / (Eⱼ₊₁ - Eⱼ)`.

The lower bound is immediate: a Lipschitz lift moves by at least the circular distance across each
gap.  The upper bound is a construction: take the shortest signed increment across each gap, which
lifts the phases without adding winding, and then extend by the McShane formula
`p(x) = minⱼ (qⱼ + L|x - Eⱼ|)`, which is exactly `L`-Lipschitz and interpolates the nodes as soon as
the nodes themselves are `L`-compatible.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

/-! ## Circular distance between phases -/

/-- The shortest signed phase increment congruent to `a - b` modulo `2π`. -/
noncomputable def phaseGap (a b : ℝ) : ℝ :=
  (a - b) - 2 * Real.pi * (round ((a - b) / (2 * Real.pi)) : ℝ)

/-- The circular geodesic distance between two phases. -/
noncomputable def circDist (a b : ℝ) : ℝ := |phaseGap a b|

theorem two_pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity

/-- The shortest increment is congruent to the naive one. -/
theorem exists_int_phaseGap (a b : ℝ) : ∃ k : ℤ, phaseGap a b = a - b + 2 * Real.pi * (k : ℝ) := by
  refine ⟨-round ((a - b) / (2 * Real.pi)), ?_⟩
  rw [phaseGap]
  push_cast
  ring

theorem circDist_nonneg (a b : ℝ) : 0 ≤ circDist a b := abs_nonneg _

/-- **The circular distance is the least admissible increment.** -/
theorem circDist_le (a b : ℝ) (k : ℤ) : circDist a b ≤ |a - b + 2 * Real.pi * (k : ℝ)| := by
  have hpi := two_pi_pos
  have hne : (2 * Real.pi) ≠ 0 := ne_of_gt hpi
  set x : ℝ := a - b with hx
  have e1 : x - 2 * Real.pi * (round (x / (2 * Real.pi)) : ℝ)
      = 2 * Real.pi * (x / (2 * Real.pi) - (round (x / (2 * Real.pi)) : ℝ)) := by
    field_simp
  have e2 : x + 2 * Real.pi * (k : ℝ)
      = 2 * Real.pi * (x / (2 * Real.pi) - ((-k : ℤ) : ℝ)) := by
    push_cast
    field_simp
    ring
  rw [circDist, phaseGap, ← hx, e1, e2, abs_mul (2 * Real.pi), abs_mul (2 * Real.pi)]
  exact mul_le_mul_of_nonneg_left (round_le (x / (2 * Real.pi)) (-k)) (abs_nonneg _)

theorem circDist_le_abs_sub (a b : ℝ) : circDist a b ≤ |a - b| := by
  have h := circDist_le a b 0
  simpa using h

/-! ## The lower bound -/

/-- A real function lifts a phase assignment through the spectrum when its node values agree with
the phases modulo `2π`. -/
def IsPhaseLift (θ E : ℕ → ℝ) (n : ℕ) (p : ℝ → ℝ) : Prop :=
  ∀ j ≤ n, ∃ k : ℤ, p (E j) = θ j + 2 * Real.pi * (k : ℝ)

/-- **Every Lipschitz lift moves by at least the circular distance across every gap.** -/
theorem circDist_le_of_lip {p : ℝ → ℝ} {L : ℝ} (hLip : ∀ x y, |p x - p y| ≤ L * |x - y|)
    {θ E : ℕ → ℝ} {n : ℕ} (hlift : IsPhaseLift θ E n p) {i j : ℕ} (hi : i ≤ n) (hj : j ≤ n) :
    circDist (θ i) (θ j) ≤ L * |E i - E j| := by
  obtain ⟨ki, hki⟩ := hlift i hi
  obtain ⟨kj, hkj⟩ := hlift j hj
  have hdiff : p (E i) - p (E j)
      = (θ i - θ j) + 2 * Real.pi * (((ki - kj : ℤ)) : ℝ) := by
    rw [hki, hkj]
    push_cast
    ring
  calc circDist (θ i) (θ j)
      ≤ |(θ i - θ j) + 2 * Real.pi * (((ki - kj : ℤ)) : ℝ)| := circDist_le _ _ _
    _ = |p (E i) - p (E j)| := by rw [hdiff]
    _ ≤ L * |E i - E j| := hLip _ _

/-! ## The shortest lift -/

/-- The lift obtained by taking the shortest signed increment across each gap. -/
noncomputable def shortestLift (θ : ℕ → ℝ) : ℕ → ℝ
  | 0 => θ 0
  | (j + 1) => shortestLift θ j + phaseGap (θ (j + 1)) (θ j)

theorem shortestLift_congr (θ : ℕ → ℝ) (j : ℕ) :
    ∃ k : ℤ, shortestLift θ j = θ j + 2 * Real.pi * (k : ℝ) := by
  induction j with
  | zero => exact ⟨0, by simp [shortestLift]⟩
  | succ j ih =>
    obtain ⟨k, hk⟩ := ih
    obtain ⟨m, hm⟩ := exists_int_phaseGap (θ (j + 1)) (θ j)
    refine ⟨k + m, ?_⟩
    rw [shortestLift, hk, hm]
    push_cast
    ring

/-- **The shortest lift is Lipschitz along the spectrum.** -/
theorem shortestLift_sub_le {θ E : ℕ → ℝ} {L : ℝ}
    (hstep : ∀ j, circDist (θ (j + 1)) (θ j) ≤ L * (E (j + 1) - E j)) :
    ∀ i j : ℕ, i ≤ j → |shortestLift θ j - shortestLift θ i| ≤ L * (E j - E i) := by
  intro i j hij
  induction j with
  | zero =>
    have : i = 0 := Nat.le_zero.mp hij
    subst this
    simp
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with hlt | hge
    · have hij' : i ≤ j := Nat.lt_succ_iff.mp hlt
      have hprev := ih hij'
      have hgap : |shortestLift θ (j + 1) - shortestLift θ j|
          ≤ L * (E (j + 1) - E j) := by
        rw [shortestLift]
        simpa [circDist] using hstep j
      have htri : |shortestLift θ (j + 1) - shortestLift θ i|
          ≤ |shortestLift θ (j + 1) - shortestLift θ j|
            + |shortestLift θ j - shortestLift θ i| := abs_sub_le _ _ _
      have : L * (E (j + 1) - E j) + L * (E j - E i) = L * (E (j + 1) - E i) := by ring
      linarith [htri, hgap, hprev]
    · have : i = j + 1 := le_antisymm hij hge
      subst this
      simp

/-! ## The McShane extension -/

/-- The McShane extension of node data with Lipschitz constant `L`. -/
noncomputable def mcShaneLift (q E : ℕ → ℝ) (L : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (Finset.range (n + 1)).inf' (by simp) fun j => q j + L * |x - E j|

/-- **The McShane extension is `L`-Lipschitz.** -/
theorem mcShaneLift_lip (q E : ℕ → ℝ) {L : ℝ} (hL : 0 ≤ L) (n : ℕ) (x y : ℝ) :
    |mcShaneLift q E L n x - mcShaneLift q E L n y| ≤ L * |x - y| := by
  have key : ∀ u v : ℝ, mcShaneLift q E L n u ≤ mcShaneLift q E L n v + L * |u - v| := by
    intro u v
    obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_inf' (s := Finset.range (n + 1))
      (by simp) fun j => q j + L * |v - E j|
    have hle : mcShaneLift q E L n u ≤ q j + L * |u - E j| :=
      Finset.inf'_le _ hj
    have htri : |u - E j| ≤ |v - E j| + |u - v| := by
      have := abs_sub_le u v (E j)
      linarith [this]
    have hstep : q j + L * |u - E j| ≤ q j + L * |v - E j| + L * |u - v| := by
      nlinarith [htri, hL]
    calc mcShaneLift q E L n u ≤ q j + L * |u - E j| := hle
      _ ≤ q j + L * |v - E j| + L * |u - v| := hstep
      _ = mcShaneLift q E L n v + L * |u - v| := by rw [mcShaneLift, ← hjeq]
  have h1 := key x y
  have h2 := key y x
  rw [abs_sub_comm y x] at h2
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- **The McShane extension interpolates compatible node data.** -/
theorem mcShaneLift_apply (q E : ℕ → ℝ) {L : ℝ} {n : ℕ}
    (hcompat : ∀ i ≤ n, ∀ j ≤ n, q i - q j ≤ L * |E i - E j|) {i : ℕ} (hi : i ≤ n) :
    mcShaneLift q E L n (E i) = q i := by
  have hmem : i ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hi)
  refine le_antisymm ?_ ?_
  · have h := Finset.inf'_le (s := Finset.range (n + 1)) (fun j => q j + L * |E i - E j|) hmem
    have hzero : q i + L * |E i - E i| = q i := by simp
    rw [mcShaneLift]
    exact le_of_le_of_eq h hzero
  · refine Finset.le_inf' _ _ fun j hj => ?_
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have := hcompat i hi j hjn
    linarith

/-! ## The bandwidth formula -/

/-- **The bandwidth is achieved.**  If the nearest-neighbour circular distances are all within `L`
times the gaps, then some `L`-Lipschitz function lifts the whole phase assignment. -/
theorem exists_phaseLift_of_step {θ E : ℕ → ℝ} {L : ℝ} {n : ℕ} (hL : 0 ≤ L)
    (hmono : ∀ j, E j ≤ E (j + 1))
    (hstep : ∀ j, circDist (θ (j + 1)) (θ j) ≤ L * (E (j + 1) - E j)) :
    ∃ p : ℝ → ℝ, (∀ x y, |p x - p y| ≤ L * |x - y|) ∧ IsPhaseLift θ E n p := by
  set q : ℕ → ℝ := shortestLift θ with hq
  have hEmono : ∀ i j : ℕ, i ≤ j → E i ≤ E j := by
    intro i j hij
    induction j with
    | zero => simp [Nat.le_zero.mp hij]
    | succ j ih =>
      rcases Nat.lt_or_ge i (j + 1) with hlt | hge
      · exact le_trans (ih (Nat.lt_succ_iff.mp hlt)) (hmono j)
      · have : i = j + 1 := le_antisymm hij hge
        subst this
        exact le_rfl
  have hcompat : ∀ i ≤ n, ∀ j ≤ n, q i - q j ≤ L * |E i - E j| := by
    intro i _ j _
    rcases le_total j i with hji | hij
    · have h := shortestLift_sub_le hstep j i hji
      have habs : |E i - E j| = E i - E j := abs_of_nonneg (by linarith [hEmono j i hji])
      rw [habs]
      have := abs_le.mp h
      linarith [this.2]
    · have h := shortestLift_sub_le hstep i j hij
      have habs : |E i - E j| = E j - E i := by
        rw [abs_sub_comm]
        exact abs_of_nonneg (by linarith [hEmono i j hij])
      rw [habs]
      have := abs_le.mp h
      linarith [this.1]
  refine ⟨mcShaneLift q E L n, mcShaneLift_lip q E hL n, fun j hj => ?_⟩
  rw [mcShaneLift_apply q E hcompat hj]
  exact shortestLift_congr θ j

/-- **The lower half of the bandwidth formula.**  Every admissible Lipschitz constant dominates
every nearest-neighbour ratio. -/
theorem step_ratio_le_of_lip {p : ℝ → ℝ} {L : ℝ} (hLip : ∀ x y, |p x - p y| ≤ L * |x - y|)
    {θ E : ℕ → ℝ} {n : ℕ} (hlift : IsPhaseLift θ E n p) (hmono : ∀ j, E j < E (j + 1))
    {j : ℕ} (hj : j + 1 ≤ n) :
    circDist (θ (j + 1)) (θ j) / (E (j + 1) - E j) ≤ L := by
  have hjn : j ≤ n := le_trans (Nat.le_succ j) hj
  have hpos : 0 < E (j + 1) - E j := by linarith [hmono j]
  have h := circDist_le_of_lip hLip hlift hj hjn
  have habs : |E (j + 1) - E j| = E (j + 1) - E j := abs_of_pos hpos
  rw [habs] at h
  exact (div_le_iff₀ hpos).mpr h

/-! ## The group laws of the circular distance -/

theorem exists_int_circDist (a b : ℝ) :
    ∃ k : ℤ, circDist a b = |a - b + 2 * Real.pi * (k : ℝ)| := by
  obtain ⟨k, hk⟩ := exists_int_phaseGap a b
  exact ⟨k, by rw [circDist, hk]⟩

theorem circDist_comm (a b : ℝ) : circDist a b = circDist b a := by
  refine le_antisymm ?_ ?_
  · obtain ⟨k, hk⟩ := exists_int_circDist b a
    have h := circDist_le a b (-k)
    have hEq : |a - b + 2 * Real.pi * ((-k : ℤ) : ℝ)| = |b - a + 2 * Real.pi * (k : ℝ)| := by
      rw [← abs_neg (b - a + 2 * Real.pi * (k : ℝ))]
      push_cast
      ring_nf
    rw [hEq, ← hk] at h
    exact h
  · obtain ⟨k, hk⟩ := exists_int_circDist a b
    have h := circDist_le b a (-k)
    have hEq : |b - a + 2 * Real.pi * ((-k : ℤ) : ℝ)| = |a - b + 2 * Real.pi * (k : ℝ)| := by
      rw [← abs_neg (a - b + 2 * Real.pi * (k : ℝ))]
      push_cast
      ring_nf
    rw [hEq, ← hk] at h
    exact h

/-- **Global phase is invisible.** -/
theorem circDist_add_const (a b c : ℝ) : circDist (a + c) (b + c) = circDist a b := by
  have h : (a + c) - (b + c) = a - b := by ring
  rw [circDist, circDist, phaseGap, phaseGap, h]

/-- **Inversion preserves the circular distance.** -/
theorem circDist_neg (a b : ℝ) : circDist (-a) (-b) = circDist a b := by
  refine le_antisymm ?_ ?_
  · obtain ⟨k, hk⟩ := exists_int_circDist a b
    have h := circDist_le (-a) (-b) (-k)
    have hEq : |(-a) - (-b) + 2 * Real.pi * ((-k : ℤ) : ℝ)|
        = |a - b + 2 * Real.pi * (k : ℝ)| := by
      rw [← abs_neg (a - b + 2 * Real.pi * (k : ℝ))]
      push_cast
      ring_nf
    rw [hEq, ← hk] at h
    exact h
  · obtain ⟨k, hk⟩ := exists_int_circDist (-a) (-b)
    have h := circDist_le a b (-k)
    have hEq : |a - b + 2 * Real.pi * ((-k : ℤ) : ℝ)|
        = |(-a) - (-b) + 2 * Real.pi * (k : ℝ)| := by
      rw [← abs_neg ((-a) - (-b) + 2 * Real.pi * (k : ℝ))]
      push_cast
      ring_nf
    rw [hEq, ← hk] at h
    exact h

/-- **Products add bandwidth.**  The circular distance is subadditive under adding phases. -/
theorem circDist_add_le (a b a' b' : ℝ) :
    circDist (a + a') (b + b') ≤ circDist a b + circDist a' b' := by
  obtain ⟨k, hk⟩ := exists_int_phaseGap a b
  obtain ⟨m, hm⟩ := exists_int_phaseGap a' b'
  have hsum : phaseGap a b + phaseGap a' b'
      = (a + a') - (b + b') + 2 * Real.pi * (((k + m : ℤ)) : ℝ) := by
    rw [hk, hm]
    push_cast
    ring
  calc circDist (a + a') (b + b')
      ≤ |(a + a') - (b + b') + 2 * Real.pi * (((k + m : ℤ)) : ℝ)| := circDist_le _ _ _
    _ = |phaseGap a b + phaseGap a' b'| := by rw [hsum]
    _ ≤ |phaseGap a b| + |phaseGap a' b'| := abs_add_le _ _
    _ = circDist a b + circDist a' b' := rfl


end GaloisForLFunctions.HTGeometry
