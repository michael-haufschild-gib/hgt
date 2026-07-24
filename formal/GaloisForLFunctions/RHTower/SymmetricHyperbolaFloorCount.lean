import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.Sqrt
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The symmetric hyperbola count for the floor-divisor summatory

The exact lattice-point identity

`∑_{d ≤ N} ⌊N/d⌋ + ⌊√N⌋² = 2·∑_{d ≤ ⌊√N⌋} ⌊N/d⌋`:

the divisor summatory counts lattice points under the hyperbola `dm ≤ N`;
every such point has `min(d,m) ≤ ⌊√N⌋`, so counting the strip `d ≤ ⌊√N⌋`
twice overcounts exactly the square `d, m ≤ ⌊√N⌋`, which lies entirely
under the hyperbola.  This is the reflection that upgrades the divisor
summatory error from `O(N)` to `O(√N)` in Dirichlet's theorem.
-/

namespace RHTower

open Finset

/-- **Symmetric hyperbola count**:
`∑_{d ≤ N} ⌊N/d⌋ + ⌊√N⌋² = 2·∑_{d ≤ ⌊√N⌋} ⌊N/d⌋`. -/
theorem sum_div_add_sqrt_sq (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 N, N / d) + Nat.sqrt N * Nat.sqrt N
      = 2 * ∑ d ∈ Finset.Icc 1 (Nat.sqrt N), N / d := by
  set s := Nat.sqrt N with hs
  have hIcc : ∀ M : ℕ, Finset.Icc 1 M = Finset.Ioc 0 M := by
    intro M
    ext d
    rw [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hIcc N, hIcc s]
  have hsN : s ≤ N := Nat.sqrt_le_self N
  have hunion : Finset.Ioc 0 s ∪ Finset.Ioc s N = Finset.Ioc 0 N :=
    Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le s) hsN
  have hdisj : Disjoint (Finset.Ioc (0 : ℕ) s) (Finset.Ioc s N) :=
    Finset.Ioc_disjoint_Ioc_of_le le_rfl
  rw [← hunion, Finset.sum_union hdisj]
  have hkey : (∑ d ∈ Finset.Ioc s N, N / d) + s * s
      = ∑ m ∈ Finset.Ioc 0 s, N / m := by
    have hcard1 : ∑ d ∈ Finset.Ioc s N, N / d
        = ((Finset.Ioc s N).sigma (fun d => Finset.Icc 1 (N / d))).card := by
      rw [Finset.card_sigma]
      apply Finset.sum_congr rfl
      intro d _
      rw [Nat.card_Icc, Nat.add_sub_cancel]
    have hcard2 :
        ((Finset.Ioc s N).sigma (fun d => Finset.Icc 1 (N / d))).card
          = ((Finset.Ioc 0 s).sigma (fun m => Finset.Ioc s (N / m))).card := by
      apply Finset.card_nbij'
        (i := fun x => ⟨x.2, x.1⟩) (j := fun y => ⟨y.2, y.1⟩)
      · rintro ⟨d, m⟩ hx
        rw [Finset.mem_coe, Finset.mem_sigma, Finset.mem_Ioc,
          Finset.mem_Icc] at hx
        dsimp only at hx
        obtain ⟨⟨hsd, hdN⟩, hm1, hmNd⟩ := hx
        rw [Finset.mem_coe, Finset.mem_sigma, Finset.mem_Ioc, Finset.mem_Ioc]
        dsimp only
        have hmd : m * d ≤ N := (Nat.le_div_iff_mul_le (by omega)).1 hmNd
        have hms : m ≤ s := by
          by_contra hms
          have hmul := Nat.mul_le_mul
            (show s + 1 ≤ m by omega) (show s + 1 ≤ d by omega)
          have hN := Nat.lt_succ_sqrt N
          rw [← hs] at hN
          have : s.succ * s.succ = (s + 1) * (s + 1) := rfl
          omega
        refine ⟨⟨by omega, hms⟩, hsd, ?_⟩
        rw [Nat.le_div_iff_mul_le (by omega : 0 < m)]
        rw [mul_comm] at hmd
        exact hmd
      · rintro ⟨m, d⟩ hy
        rw [Finset.mem_coe, Finset.mem_sigma, Finset.mem_Ioc,
          Finset.mem_Ioc] at hy
        dsimp only at hy
        obtain ⟨⟨hm0, hms⟩, hsd, hdNm⟩ := hy
        rw [Finset.mem_coe, Finset.mem_sigma, Finset.mem_Ioc, Finset.mem_Icc]
        dsimp only
        have hdm : d * m ≤ N := (Nat.le_div_iff_mul_le (by omega)).1 hdNm
        refine ⟨⟨hsd, ?_⟩, by omega, ?_⟩
        · calc d ≤ N / m := hdNm
            _ ≤ N := Nat.div_le_self N m
        · rw [Nat.le_div_iff_mul_le (by omega : 0 < d)]
          rw [mul_comm] at hdm
          exact hdm
      · rintro ⟨d, m⟩ _
        rfl
      · rintro ⟨m, d⟩ _
        rfl
    have hcard3 :
        ((Finset.Ioc 0 s).sigma (fun m => Finset.Ioc s (N / m))).card
          = ∑ m ∈ Finset.Ioc 0 s, (N / m - s) := by
      rw [Finset.card_sigma]
      apply Finset.sum_congr rfl
      intro m _
      rw [Nat.card_Ioc]
    have hge : ∀ m ∈ Finset.Ioc 0 s, s ≤ N / m := by
      intro m hm
      rw [Finset.mem_Ioc] at hm
      rw [Nat.le_div_iff_mul_le (by omega : 0 < m)]
      calc s * m ≤ s * s := Nat.mul_le_mul_left s hm.2
        _ ≤ N := by
          rw [hs]
          exact Nat.sqrt_le N
    have hcards : (Finset.Ioc (0 : ℕ) s).card = s := by
      rw [Nat.card_Ioc]
      omega
    rw [hcard1, hcard2, hcard3]
    calc (∑ m ∈ Finset.Ioc 0 s, (N / m - s)) + s * s
        = (∑ m ∈ Finset.Ioc 0 s, (N / m - s))
            + ∑ _m ∈ Finset.Ioc 0 s, s := by
          rw [Finset.sum_const_nat (m := s) (fun _ _ => rfl), hcards]
      _ = ∑ m ∈ Finset.Ioc 0 s, ((N / m - s) + s) :=
          Finset.sum_add_distrib.symm
      _ = ∑ m ∈ Finset.Ioc 0 s, N / m := by
          apply Finset.sum_congr rfl
          intro m hm
          have := hge m hm
          omega
  omega

end RHTower
