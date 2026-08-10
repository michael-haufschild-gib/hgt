import GaloisForLFunctions.RHTower.BeurlingSystemGibbsGauge

/-!
# Counting and absolute convergence for a discrete Beurling system

A discrete Beurling system has only finitely many generalized integers of bounded norm, and its
counting function grows at most linearly.  That alone makes every exponential Gibbs sum over the
generalized integers absolutely convergent: grouping the integers into unit norm layers turns the
sum into a geometric series with linear layer weights.
-/

open scoped BigOperators

namespace RHTower

namespace BeurlingSystem

variable (B : BeurlingSystem)

/-- A Beurling system is discrete when only finitely many generalized integers have bounded
norm. -/
def IsDiscrete : Prop := ∀ X : ℝ, {g : Multiset B.Label | B.intNorm g ≤ X}.Finite

open scoped Classical in
/-- The generalized-integer counting function `N(X)`. -/
noncomputable def countBall (X : ℝ) : ℕ := Set.ncard {g : Multiset B.Label | B.intNorm g ≤ X}

/-- Linear growth of the counting function, the only consequence of `(BF1)` needed for absolute
convergence. -/
def HasLinearCounting (C : ℝ) : Prop := ∀ X : ℝ, 1 ≤ X → (B.countBall X : ℝ) ≤ C * X

variable {B}

theorem countBall_mono (hdisc : B.IsDiscrete) {X Y : ℝ} (hXY : X ≤ Y) :
    B.countBall X ≤ B.countBall Y := by
  classical
  refine Set.ncard_le_ncard (fun g hg => le_trans hg hXY) (hdisc Y)

/-- Every generalized integer lies in the unit layer indexed by the floor of its norm. -/
theorem intNorm_lt_floor_add_one (g : Multiset B.Label) :
    B.intNorm g < (⌊B.intNorm g⌋₊ : ℝ) + 1 :=
  Nat.lt_floor_add_one _

theorem floor_le_intNorm (g : Multiset B.Label) : ((⌊B.intNorm g⌋₊ : ℝ)) ≤ B.intNorm g :=
  Nat.floor_le (le_trans zero_le_one (B.one_le_intNorm g))

/-- **Absolute convergence of the exponential Gibbs sum.**  Linear counting makes the layer sums
geometric. -/
theorem summable_expNegNorm (hdisc : B.IsDiscrete) {C : ℝ} (hC : B.HasLinearCounting C)
    {x : ℝ} (hx : 0 < x) :
    Summable fun g : Multiset B.Label => Real.exp (-x * B.intNorm g) := by
  classical
  set r : ℝ := Real.exp (-x) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by
    rw [hr]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  -- the layer bound series
  have hgeom : Summable fun n : ℕ => C * ((n : ℝ) + 1) * r ^ n := by
    have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
      (by rwa [Real.norm_eq_abs, abs_of_pos hr0])
    have h2 : Summable fun n : ℕ => ((n : ℝ) + 1) * r ^ n := by
      refine (h.add (summable_geometric_of_lt_one hr0.le hr1)).congr fun n => ?_
      simp only [pow_one]
      ring
    simpa [mul_assoc] using h2.mul_left C
  set K : ℝ := ∑' n : ℕ, C * ((n : ℝ) + 1) * r ^ n with hK
  refine summable_of_sum_le (c := K) (fun g => (Real.exp_pos _).le) fun S => ?_
  -- group the finite set by norm layer
  have hmaps : ∀ g ∈ S, ⌊B.intNorm g⌋₊ ∈ S.image fun g => ⌊B.intNorm g⌋₊ := by
    intro g hg
    exact Finset.mem_image_of_mem _ hg
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hlayer : ∀ n ∈ S.image fun g => ⌊B.intNorm g⌋₊,
      ∑ g ∈ S with ⌊B.intNorm g⌋₊ = n, Real.exp (-x * B.intNorm g) ≤ C * ((n : ℝ) + 1) * r ^ n := by
    intro n _
    have hterm : ∀ g ∈ S.filter fun g => ⌊B.intNorm g⌋₊ = n,
        Real.exp (-x * B.intNorm g) ≤ r ^ n := by
      intro g hg
      have hgn : ⌊B.intNorm g⌋₊ = n := (Finset.mem_filter.mp hg).2
      have hge : (n : ℝ) ≤ B.intNorm g := by
        rw [← hgn]
        exact floor_le_intNorm g
      rw [hr, ← Real.exp_nat_mul]
      refine Real.exp_le_exp.mpr ?_
      nlinarith
    have hcard : ((S.filter fun g => ⌊B.intNorm g⌋₊ = n).card : ℝ) ≤ C * ((n : ℝ) + 1) := by
      have hballfin := hdisc ((n : ℝ) + 1)
      have hcards : (S.filter fun g => ⌊B.intNorm g⌋₊ = n).card ≤ B.countBall ((n : ℝ) + 1) := by
        rw [countBall, Set.ncard_eq_toFinset_card _ hballfin]
        refine Finset.card_le_card fun g hg => ?_
        rw [Set.Finite.mem_toFinset]
        simp only [Finset.mem_filter] at hg
        have hgn : ⌊B.intNorm g⌋₊ = n := hg.2
        have hlt := intNorm_lt_floor_add_one (B := B) g
        rw [hgn] at hlt
        exact hlt.le
      have hone : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        have := Nat.cast_nonneg (α := ℝ) n
        linarith
      have hbound := hC ((n : ℝ) + 1) hone
      calc ((S.filter fun g => ⌊B.intNorm g⌋₊ = n).card : ℝ)
          ≤ (B.countBall ((n : ℝ) + 1) : ℝ) := by exact_mod_cast hcards
        _ ≤ C * ((n : ℝ) + 1) := hbound
    calc ∑ g ∈ S with ⌊B.intNorm g⌋₊ = n, Real.exp (-x * B.intNorm g)
        ≤ ∑ g ∈ S with ⌊B.intNorm g⌋₊ = n, r ^ n := Finset.sum_le_sum hterm
      _ = ((S.filter fun g => ⌊B.intNorm g⌋₊ = n).card : ℝ) * r ^ n := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (C * ((n : ℝ) + 1)) * r ^ n := by
          have hrn : (0 : ℝ) ≤ r ^ n := (pow_pos hr0 n).le
          exact mul_le_mul_of_nonneg_right hcard hrn
      _ = C * ((n : ℝ) + 1) * r ^ n := by ring
  calc ∑ n ∈ S.image (fun g => ⌊B.intNorm g⌋₊),
        ∑ g ∈ S with ⌊B.intNorm g⌋₊ = n, Real.exp (-x * B.intNorm g)
      ≤ ∑ n ∈ S.image (fun g => ⌊B.intNorm g⌋₊), C * ((n : ℝ) + 1) * r ^ n :=
        Finset.sum_le_sum hlayer
    _ ≤ K := by
        refine hgeom.sum_le_tsum _ (fun n _ => ?_)
        have : (0 : ℝ) ≤ r ^ n := (pow_pos hr0 n).le
        have hC0 : 0 ≤ C := by
          have := hC 1 le_rfl
          have hpos : (0 : ℝ) ≤ (B.countBall 1 : ℝ) := Nat.cast_nonneg _
          linarith
        positivity

end BeurlingSystem

end RHTower
