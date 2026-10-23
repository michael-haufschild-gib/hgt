import GaloisForLFunctions.SignedArithmeticEnergyIncidence.FrustratedCyclesSpoilLocalPayment

/-!
# Frustration is paid along canonical paths

Local payment pays each overlap from the two budgets at its ends; on a frustrated pattern that
fails.  The nonlocal payment of `TheFrustratedCycleIsPaidAlongItsPath` pays the frustrated edge
of one cycle by the Dirichlet energy of the path closing it.  Here the same mechanism is a
certificate for an arbitrary symmetric form with any number of frustrated cycles, sharing edges or
not: the **signed canonical-path method**.

A `PathCertificate` consists of

* a positive gauge `v` that is a signed supersolution, `(Cv)_i ≥ 0`;
* for every anti-aligned overlap `a, b` (`c_ab > 0`) a walk from `a` to `b` through aligned
  overlaps (`c < 0`), and shares `λ_ab(x, y) > 0` of the aligned overlaps it uses;
* the **path budget** `c_ab v_a v_b Σ_steps 1/(λ_ab |c_xy| v_x v_y) ≤ 1` of each anti-aligned
  overlap;
* the **packing** `Σ_{a,b} Σ_steps λ_ab(x, y) ≤ 1` of each aligned overlap: paths through a shared
  edge split its Dirichlet energy.

In the gauge `f = v g` the energy is `Σ v_i (Cv)_i g_i²` plus the aligned Dirichlet energy minus
the anti-aligned one (`incidenceEnergy_mul_eq`).  Cauchy–Schwarz along each path bounds an
anti-aligned term by its shares of the aligned terms on the path (`antiTerm_le_pathEnergy`), and
the packing keeps every aligned term from being spent twice
(`incidenceEnergy_nonneg_of_pathCertificate`).  Competition between frustrated cycles sharing
edges is exactly the packing constraint.
-/

open Finset

namespace GaloisForLFunctions.SignedArithmeticEnergyIncidence

noncomputable section
set_option autoImplicit false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A signed canonical-path certificate of positivity. -/
structure PathCertificate (c : ι → ι → ℝ) where
  /-- The positive gauge. -/
  gauge : ι → ℝ
  gauge_pos : ∀ i, 0 < gauge i
  /-- The gauge is a signed supersolution. -/
  supersolution : ∀ i, 0 ≤ couplingAction c gauge i
  /-- The canonical path of an anti-aligned overlap. -/
  path : ι → ι → List ι
  /-- The share `λ_ab(x, y)` of the aligned overlap `x y` given to the anti-aligned overlap `a b`. -/
  share : ι → ι → ι → ι → ℝ
  path_end : ∀ a b, a ≠ b → 0 < c a b → walkEnd a (path a b) = b
  path_aligned : ∀ a b, a ≠ b → 0 < c a b → ∀ s < (path a b).length,
    c (walkVertex a (path a b) s) (walkVertex a (path a b) (s + 1)) < 0
  share_pos : ∀ a b, a ≠ b → 0 < c a b → ∀ s < (path a b).length,
    0 < share a b (walkVertex a (path a b) s) (walkVertex a (path a b) (s + 1))
  /-- The path budget of every anti-aligned overlap. -/
  budget : ∀ a b, a ≠ b → 0 < c a b →
    c a b * gauge a * gauge b * ∑ s ∈ range (path a b).length,
      1 / (share a b (walkVertex a (path a b) s) (walkVertex a (path a b) (s + 1)) *
        (|c (walkVertex a (path a b) s) (walkVertex a (path a b) (s + 1))| *
          gauge (walkVertex a (path a b) s) * gauge (walkVertex a (path a b) (s + 1)))) ≤ 1
  /-- The packing of every aligned overlap. -/
  packing : ∀ x y, ∑ a, ∑ b, (if a ≠ b ∧ 0 < c a b then
    ∑ s ∈ range (path a b).length, (if walkVertex a (path a b) s = x ∧
      walkVertex a (path a b) (s + 1) = y then share a b x y else 0) else 0) ≤ 1

/-- Summing over the steps of a walk is summing over ordered pairs with step multiplicities. -/
theorem sum_steps_eq (z : ℕ → ι) (L : ℕ) (F : ι → ι → ℝ) :
    ∑ s ∈ range L, F (z s) (z (s + 1)) =
      ∑ x, ∑ y, ∑ s ∈ range L, (if z s = x ∧ z (s + 1) = y then F x y else 0) := by
  calc ∑ s ∈ range L, F (z s) (z (s + 1))
      = ∑ s ∈ range L, ∑ x, ∑ y, (if z s = x ∧ z (s + 1) = y then F x y else 0) := by
        refine sum_congr rfl fun s _ => ?_
        rw [sum_eq_single (z s) (fun x _ hx => sum_eq_zero fun y _ => if_neg fun h => hx h.1.symm)
          (fun h => absurd (mem_univ _) h),
          sum_eq_single (z (s + 1)) (fun y _ hy => if_neg fun h => hy h.2.symm)
          (fun h => absurd (mem_univ _) h), if_pos ⟨rfl, rfl⟩]
    _ = ∑ x, ∑ s ∈ range L, ∑ y, (if z s = x ∧ z (s + 1) = y then F x y else 0) := sum_comm
    _ = _ := sum_congr rfl fun x _ => sum_comm

omit [DecidableEq ι] in
/-- Exchanging two pairs of summation indices. -/
theorem sum_swap4 (T : ι → ι → ι → ι → ℝ) :
    ∑ a, ∑ b, ∑ x, ∑ y, T a b x y = ∑ x, ∑ y, ∑ a, ∑ b, T a b x y :=
  calc ∑ a, ∑ b, ∑ x, ∑ y, T a b x y = ∑ a, ∑ x, ∑ b, ∑ y, T a b x y :=
        sum_congr rfl fun _ _ => sum_comm
    _ = ∑ x, ∑ a, ∑ b, ∑ y, T a b x y := sum_comm
    _ = ∑ x, ∑ a, ∑ y, ∑ b, T a b x y :=
        sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => sum_comm
    _ = ∑ x, ∑ y, ∑ a, ∑ b, T a b x y := sum_congr rfl fun _ _ => sum_comm

/-- **Cauchy–Schwarz along a canonical path**: an anti-aligned term is at most its shares of the
aligned Dirichlet terms on its path. -/
theorem antiTerm_le_pathEnergy {c : ι → ι → ℝ} (P : PathCertificate c) (g : ι → ℝ) {a b : ι}
    (hab : a ≠ b) (hc : 0 < c a b) :
    c a b * P.gauge a * P.gauge b * (g a - g b) ^ 2 ≤
      ∑ s ∈ range (P.path a b).length,
        P.share a b (walkVertex a (P.path a b) s) (walkVertex a (P.path a b) (s + 1)) *
          (|c (walkVertex a (P.path a b) s) (walkVertex a (P.path a b) (s + 1))| *
            P.gauge (walkVertex a (P.path a b) s) * P.gauge (walkVertex a (P.path a b) (s + 1))) *
          (g (walkVertex a (P.path a b) s) - g (walkVertex a (P.path a b) (s + 1))) ^ 2 := by
  set l := P.path a b
  set z := walkVertex a l
  set W : ℕ → ℝ := fun s => P.share a b (z s) (z (s + 1)) *
    (|c (z s) (z (s + 1))| * P.gauge (z s) * P.gauge (z (s + 1))) with hW
  have hWpos : ∀ s ∈ range l.length, 0 < W s := fun s hs => by
    have hs' := mem_range.1 hs
    exact mul_pos (P.share_pos a b hab hc s hs') (mul_pos (mul_pos
      (abs_pos.2 (P.path_aligned a b hab hc s hs').ne) (P.gauge_pos _)) (P.gauge_pos _))
  -- the difference telescopes along the path
  have htel : g a - g b = ∑ s ∈ range l.length, (g (z s) - g (z (s + 1))) := by
    rw [sum_range_sub' (fun s => g (z s)) l.length]
    have h0 : z 0 = a := by simp only [z, walkVertex]
    have hL : z l.length = b := by simp only [z]; rw [walkVertex_length, P.path_end a b hab hc]
    rw [h0, hL]
  have hlen : 0 < l.length := by
    rcases Nat.eq_zero_or_pos l.length with h | h
    · have hend := P.path_end a b hab hc
      change walkEnd a l = b at hend
      rw [List.length_eq_zero_iff.1 h] at hend
      exact absurd hend hab
    · exact h
  have hu : ∀ s ∈ range l.length, 0 < 1 / W s := fun s hs => one_div_pos.2 (hWpos s hs)
  have hpos : 0 < ∑ s ∈ range l.length, 1 / W s := sum_pos hu (nonempty_range_iff.2 hlen.ne')
  have hcs := sq_sum_div_le_sum_sq_div (range l.length) (fun s => g (z s) - g (z (s + 1))) hu
  rw [div_le_iff₀ hpos] at hcs
  have hrhs : ∑ s ∈ range l.length, (g (z s) - g (z (s + 1))) ^ 2 / (1 / W s) =
      ∑ s ∈ range l.length, W s * (g (z s) - g (z (s + 1))) ^ 2 :=
    sum_congr rfl fun s _ => by rw [div_div_eq_mul_div, div_one, mul_comm]
  rw [hrhs, ← htel] at hcs
  have hD : 0 ≤ ∑ s ∈ range l.length, W s * (g (z s) - g (z (s + 1))) ^ 2 :=
    sum_nonneg fun s hs => mul_nonneg (hWpos s hs).le (sq_nonneg _)
  have hcvv : 0 ≤ c a b * P.gauge a * P.gauge b :=
    (mul_pos (mul_pos hc (P.gauge_pos a)) (P.gauge_pos b)).le
  have hbud := P.budget a b hab hc
  calc c a b * P.gauge a * P.gauge b * (g a - g b) ^ 2
      ≤ c a b * P.gauge a * P.gauge b *
          ((∑ s ∈ range l.length, W s * (g (z s) - g (z (s + 1))) ^ 2) *
            ∑ s ∈ range l.length, 1 / W s) := mul_le_mul_of_nonneg_left hcs hcvv
    _ = (c a b * P.gauge a * P.gauge b * ∑ s ∈ range l.length, 1 / W s) *
          ∑ s ∈ range l.length, W s * (g (z s) - g (z (s + 1))) ^ 2 := by ring
    _ ≤ 1 * ∑ s ∈ range l.length, W s * (g (z s) - g (z (s + 1))) ^ 2 :=
          mul_le_mul_of_nonneg_right hbud hD
    _ = _ := one_mul _

/-- **Signed canonical-path positivity**: a form with a path certificate is nonnegative. -/
theorem incidenceEnergy_nonneg_of_pathCertificate {c : ι → ι → ℝ} (hc : IsSymmetricCoupling c)
    (P : PathCertificate c) (f : ι → ℝ) : 0 ≤ incidenceEnergy c f := by
  set v := P.gauge
  set g : ι → ℝ := fun i => f i / v i
  have hf : f = fun i => v i * g i := funext fun i => by
    have hv : v i ≠ 0 := (P.gauge_pos i).ne'
    simp only [g]
    field_simp
  set w : ι → ι → ℝ := fun x y => |c x y| * v x * v y
  set D : ι → ι → ℝ := fun x y => (g x - g y) ^ 2
  -- the anti-aligned and aligned parts of the Dirichlet sum
  set anti : ι → ι → ℝ := fun i j => if i ≠ j ∧ 0 < c i j then c i j * v i * v j * D i j else 0
  set ali : ι → ι → ℝ := fun i j => if c i j < 0 then w i j * D i j else 0
  have hsplit : ∀ i j, c i j * v i * v j * D i j = anti i j - ali i j := by
    intro i j
    by_cases hij : i = j
    · subst hij
      simp only [D, anti, ali, w, sub_self, ne_eq, not_true_eq_false, false_and, if_false]
      split_ifs <;> ring
    rcases lt_trichotomy (c i j) 0 with hneg | hzero | hpos
    · simp only [anti, ali, w, if_pos hneg, if_neg (fun h : i ≠ j ∧ 0 < c i j => absurd h.2
        (not_lt.2 hneg.le)), abs_of_neg hneg]
      ring
    · simp only [anti, ali, hzero, lt_irrefl, and_false, if_false]; ring
    · simp only [anti, ali, if_pos (show i ≠ j ∧ 0 < c i j from ⟨hij, hpos⟩),
        if_neg (not_lt.2 hpos.le)]
      ring
  -- every anti-aligned term is paid by its path shares
  have hanti : ∑ a, ∑ b, anti a b ≤ ∑ x, ∑ y, ali x y := by
    have h1 : ∀ a b, anti a b ≤ if a ≠ b ∧ 0 < c a b then
        ∑ x, ∑ y, ∑ s ∈ range (P.path a b).length,
          (if walkVertex a (P.path a b) s = x ∧ walkVertex a (P.path a b) (s + 1) = y then
            P.share a b x y * w x y * D x y else 0) else 0 := by
      intro a b
      simp only [anti]
      split_ifs with h
      · rw [← sum_steps_eq (walkVertex a (P.path a b)) (P.path a b).length
          (fun x y => P.share a b x y * w x y * D x y)]
        exact antiTerm_le_pathEnergy P g h.1 h.2
      · exact le_refl 0
    have h2 : ∀ x y, (∑ a, ∑ b, if a ≠ b ∧ 0 < c a b then
        ∑ s ∈ range (P.path a b).length,
          (if walkVertex a (P.path a b) s = x ∧ walkVertex a (P.path a b) (s + 1) = y then
            P.share a b x y * w x y * D x y else 0) else 0) ≤ ali x y := by
      intro x y
      have hfac : (∑ a, ∑ b, if a ≠ b ∧ 0 < c a b then
          ∑ s ∈ range (P.path a b).length,
            (if walkVertex a (P.path a b) s = x ∧ walkVertex a (P.path a b) (s + 1) = y then
              P.share a b x y * w x y * D x y else 0) else 0) =
          (∑ a, ∑ b, if a ≠ b ∧ 0 < c a b then
            ∑ s ∈ range (P.path a b).length,
              (if walkVertex a (P.path a b) s = x ∧ walkVertex a (P.path a b) (s + 1) = y then
                P.share a b x y else 0) else 0) * (w x y * D x y) := by
        rw [sum_mul]
        refine sum_congr rfl fun a _ => ?_
        rw [sum_mul]
        refine sum_congr rfl fun b _ => ?_
        split_ifs
        · rw [sum_mul]
          refine sum_congr rfl fun s _ => ?_
          split_ifs <;> ring
        · ring
      rw [hfac]
      have hwD : 0 ≤ w x y * D x y := mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _)
        (P.gauge_pos x).le) (P.gauge_pos y).le) (sq_nonneg _)
      by_cases hxy : c x y < 0
      · simp only [ali, if_pos hxy]
        calc _ ≤ 1 * (w x y * D x y) := mul_le_mul_of_nonneg_right (P.packing x y) hwD
          _ = _ := one_mul _
      · -- no canonical path uses an overlap that is not aligned
        have hzero : (∑ a, ∑ b, if a ≠ b ∧ 0 < c a b then
            ∑ s ∈ range (P.path a b).length,
              (if walkVertex a (P.path a b) s = x ∧ walkVertex a (P.path a b) (s + 1) = y then
                P.share a b x y else 0) else 0) = 0 := by
          refine sum_eq_zero fun a _ => sum_eq_zero fun b _ => ?_
          split_ifs with hab
          · refine sum_eq_zero fun s hs => if_neg fun hst => hxy ?_
            have := P.path_aligned a b hab.1 hab.2 s (mem_range.1 hs)
            rwa [hst.1, hst.2] at this
          · rfl
        simp only [ali, if_neg hxy, hzero, zero_mul, le_refl]
    calc ∑ a, ∑ b, anti a b
        ≤ ∑ a, ∑ b, (if a ≠ b ∧ 0 < c a b then
          ∑ x, ∑ y, ∑ s ∈ range (P.path a b).length,
            (if walkVertex a (P.path a b) s = x ∧ walkVertex a (P.path a b) (s + 1) = y then
              P.share a b x y * w x y * D x y else 0) else 0) :=
          sum_le_sum fun a _ => sum_le_sum fun b _ => h1 a b
      _ = ∑ x, ∑ y, ∑ a, ∑ b, (if a ≠ b ∧ 0 < c a b then
          ∑ s ∈ range (P.path a b).length,
            (if walkVertex a (P.path a b) s = x ∧ walkVertex a (P.path a b) (s + 1) = y then
              P.share a b x y * w x y * D x y else 0) else 0) := by
          -- move the pair `(x, y)` outside
          have e : ∀ a b, (if a ≠ b ∧ 0 < c a b then
              ∑ x, ∑ y, ∑ s ∈ range (P.path a b).length,
                (if walkVertex a (P.path a b) s = x ∧ walkVertex a (P.path a b) (s + 1) = y then
                  P.share a b x y * w x y * D x y else 0) else 0) =
              ∑ x, ∑ y, (if a ≠ b ∧ 0 < c a b then
                ∑ s ∈ range (P.path a b).length,
                  (if walkVertex a (P.path a b) s = x ∧ walkVertex a (P.path a b) (s + 1) = y then
                    P.share a b x y * w x y * D x y else 0) else 0) := by
            intro a b
            by_cases h : a ≠ b ∧ 0 < c a b
            · simp only [if_pos h]
            · simp only [if_neg h, sum_const_zero]
          simp only [e]
          exact sum_swap4 _
      _ ≤ ∑ x, ∑ y, ali x y := sum_le_sum fun x _ => sum_le_sum fun y _ => h2 x y
  -- assemble through the ground-state transform
  rw [hf, incidenceEnergy_mul_eq hc]
  have hA : 0 ≤ ∑ i, v i * couplingAction c v i * g i ^ 2 :=
    sum_nonneg fun i _ => mul_nonneg (mul_nonneg (P.gauge_pos i).le (P.supersolution i))
      (sq_nonneg _)
  have hS : ∑ i, ∑ j, c i j * v i * v j * (g i - g j) ^ 2 =
      ∑ a, ∑ b, anti a b - ∑ x, ∑ y, ali x y := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by rw [← sum_sub_distrib]; exact sum_congr rfl fun j _ => hsplit i j
  rw [hS]
  linarith

end

end GaloisForLFunctions.SignedArithmeticEnergyIncidence
