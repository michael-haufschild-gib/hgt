import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenC1Coefficient
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenC2Coefficient

/-!
# Exact Matomäki--Teräväinen Lemma 2.3(i) algebra

This file proves the literal complex identity behind Lemma 2.3(i).  It reindexes Buchstab's
prime remainder from divisor-first to prime-first form, separates lower and upper endpoint spills,
and identifies the three source errors `c₁,n`, `c₂,n`, and `c₃,n` with their exact signs.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- Swap the two visible factors in a divisor-of-a-quotient sum. -/
theorem sum_divisors_quotient_swap
    {M : Type*} [AddCommMonoid M] {n : ℕ} (hn : 0 < n) (f : ℕ → ℕ → M) :
    ∑ a ∈ n.divisors, ∑ b ∈ (n / a).divisors, f a b =
      ∑ b ∈ n.divisors, ∑ a ∈ (n / b).divisors, f a b := by
  classical
  rw [Finset.sum_sigma' n.divisors (fun a => (n / a).divisors) (fun a b => f a b),
    Finset.sum_sigma' n.divisors (fun b => (n / b).divisors) (fun b a => f a b)]
  refine Finset.sum_nbij' (i := fun x => ⟨x.2, x.1⟩) (j := fun x => ⟨x.2, x.1⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨a, b⟩ hx
    simp only [Finset.mem_sigma, Nat.mem_divisors] at hx ⊢
    obtain ⟨⟨haN, -⟩, hbq, hq0⟩ := hx
    have hqa : n / a ∣ n := by
      refine ⟨a, ?_⟩
      exact (Nat.div_mul_cancel haN).symm
    have hbN : b ∣ n := hbq.trans hqa
    have hb0 : b ≠ 0 := fun hb => hq0 (Nat.eq_zero_of_zero_dvd (hb ▸ hbq))
    have habN : a * b ∣ n := (Nat.dvd_div_iff_mul_dvd haN).mp hbq
    have haqb : a ∣ n / b :=
      (Nat.dvd_div_iff_mul_dvd hbN).mpr (by simpa [Nat.mul_comm] using habN)
    have hqb0 : n / b ≠ 0 :=
      (Nat.div_pos (Nat.le_of_dvd hn hbN) (Nat.pos_of_ne_zero hb0)).ne'
    exact ⟨⟨hbN, hn.ne'⟩, haqb, hqb0⟩
  · rintro ⟨b, a⟩ hx
    simp only [Finset.mem_sigma, Nat.mem_divisors] at hx ⊢
    obtain ⟨⟨hbN, -⟩, haq, hq0⟩ := hx
    have hqb : n / b ∣ n := by
      refine ⟨b, ?_⟩
      exact (Nat.div_mul_cancel hbN).symm
    have haN : a ∣ n := haq.trans hqb
    have ha0 : a ≠ 0 := fun ha => hq0 (Nat.eq_zero_of_zero_dvd (ha ▸ haq))
    have hbaN : b * a ∣ n := (Nat.dvd_div_iff_mul_dvd hbN).mp haq
    have hbqa : b ∣ n / a :=
      (Nat.dvd_div_iff_mul_dvd haN).mpr (by simpa [Nat.mul_comm] using hbaN)
    have hqa0 : n / a ≠ 0 :=
      (Nat.div_pos (Nat.le_of_dvd hn haN) (Nat.pos_of_ne_zero ha0)).ne'
    exact ⟨⟨haN, hn.ne'⟩, hbqa, hqa0⟩
  · rintro ⟨a, b⟩ _
    rfl
  · rintro ⟨b, a⟩ _
    rfl
  · rintro ⟨a, b⟩ _
    rfl

/-- A finite prime family can be intersected with the divisors of `n` from either side. -/
theorem sum_divisors_indicator_eq_sum_finset_dvd
    {M : Type*} [AddCommMonoid M] {n : ℕ} (hn : 0 < n)
    (S : Finset ℕ) (f : ℕ → M) :
    ∑ q ∈ n.divisors, (if q ∈ S then f q else (0 : M)) =
      ∑ q ∈ S, (if q ∣ n then f q else (0 : M)) := by
  classical
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  apply Finset.sum_congr
  · ext q
    rw [Finset.mem_filter, Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hq, -⟩, hS⟩
      exact ⟨hS, hq⟩
    · rintro ⟨hS, hq⟩
      exact ⟨⟨hq, hn.ne'⟩, hS⟩
  · intro q hq
    rfl

/-- A prime window is the corresponding filter of the positive quotient's divisor set. -/
theorem primeWindow_eq_divisors_filter {k a b : ℕ} (hk : 0 < k) :
    primeWindow k a b = k.divisors.filter (fun q => q ∈ primesIco a b) := by
  ext q
  rw [mem_primeWindow, Finset.mem_filter, Nat.mem_divisors, mem_primesIco]
  constructor
  · rintro ⟨⟨ha, hb⟩, hp, hq⟩
    exact ⟨⟨hq, hk.ne'⟩, ha, hb, hp⟩
  · rintro ⟨⟨hq, -⟩, ha, hb, hp⟩
    exact ⟨⟨ha, hb⟩, hp, hq⟩

/-- Buchstab's divisor-first prime remainder equals the literal prime-first boundary coefficient. -/
theorem primeRemainder_eq_mtC2BoundaryCoefficient
    (α : ℕ → ℂ) (level : ℕ → ℕ) {n a b : ℕ} (hn : 0 < n) :
    (∑ m ∈ n.divisors, ∑ q ∈ primeWindow (n / m) a b,
        α m * (rho ((n / m) / q) (level q) : ℂ)) =
      mtC2BoundaryCoefficient α (primesIco a b) level n := by
  have hquot : ∀ m ∈ n.divisors, 0 < n / m := by
    intro m hm
    exact Nat.div_pos (Nat.le_of_dvd hn (Nat.mem_divisors.mp hm).1)
      (Nat.pos_of_mem_divisors hm)
  calc
    (∑ m ∈ n.divisors, ∑ q ∈ primeWindow (n / m) a b,
        α m * (rho ((n / m) / q) (level q) : ℂ)) =
      ∑ m ∈ n.divisors, ∑ q ∈ (n / m).divisors,
        if q ∈ primesIco a b then
          α m * (rho ((n / m) / q) (level q) : ℂ) else 0 := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [primeWindow_eq_divisors_filter (hquot m hm), Finset.sum_filter]
    _ = ∑ q ∈ n.divisors, ∑ m ∈ (n / q).divisors,
        if q ∈ primesIco a b then
          α m * (rho ((n / q) / m) (level q) : ℂ) else 0 := by
      simpa only [Nat.div_div_eq_div_mul, mul_comm] using
        (sum_divisors_quotient_swap hn (fun m q =>
          if q ∈ primesIco a b then
            α m * (rho ((n / m) / q) (level q) : ℂ) else 0))
    _ = ∑ q ∈ primesIco a b, if q ∣ n then
        ∑ m ∈ (n / q).divisors,
          α m * (rho ((n / q) / m) (level q) : ℂ) else 0 := by
      rw [show (∑ q ∈ n.divisors, ∑ m ∈ (n / q).divisors,
          if q ∈ primesIco a b then
            α m * (rho ((n / q) / m) (level q) : ℂ) else 0) =
          ∑ q ∈ n.divisors, if q ∈ primesIco a b then
            (∑ m ∈ (n / q).divisors,
              α m * (rho ((n / q) / m) (level q) : ℂ)) else 0 by
        apply Finset.sum_congr rfl
        intro q hq
        split_ifs <;> simp]
      exact sum_divisors_indicator_eq_sum_finset_dvd hn _ _
    _ = mtC2BoundaryCoefficient α (primesIco a b) level n := by
      rfl

/-- Buchstab plus truncated Legendre expansion, before adic endpoint alignment. -/
theorem buchstab_c1_decomposition
    (α : ℕ → ℂ) {n z₀ z₁ D : ℕ} (hn : 0 < n) (hz : z₀ ≤ z₁) :
    (∑ m ∈ n.divisors, α m * (rho (n / m) z₁ : ℂ)) =
      (∑ m ∈ n.divisors, α m * (truncLegendre (n / m) z₀ D : ℂ)) -
        mtC2BoundaryCoefficient α (primesIco z₀ z₁) id n +
        mtC1Coefficient α z₀ D n := by
  rw [← primeRemainder_eq_mtC2BoundaryCoefficient α id hn]
  unfold mtC1Coefficient
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  have hmDvd : m ∣ n := (Nat.mem_divisors.mp hm).1
  have hk : 0 < n / m :=
    Nat.div_pos (Nat.le_of_dvd hn hmDvd) (Nat.pos_of_mem_divisors hm)
  have hbuch := buchstab_window (n := n / m) (w := z₀) (z := z₁) hk hz
  have hbuchC :
      (rho (n / m) z₁ : ℂ) +
          ∑ q ∈ primeWindow (n / m) z₀ z₁, (rho ((n / m) / q) q : ℂ) =
        (rho (n / m) z₀ : ℂ) := by
    exact_mod_cast hbuch
  rw [← Finset.mul_sum, ← hbuchC]
  simp only [id_eq]
  ring

/-- Adding the upper spill and deleting the lower spill is exactly the source's `c₂,n`. -/
theorem mtC2Boundary_main_eq_clipped_add_mtC2
    (α : ℕ → ℂ) (P lowerSpill upperSpill : Finset ℕ) (level : ℕ → ℕ) (n : ℕ)
    (hlower : lowerSpill ⊆ P)
    (hdisj : Disjoint (P \ lowerSpill) upperSpill) :
    mtC2BoundaryCoefficient α ((P \ lowerSpill) ∪ upperSpill) level n =
      mtC2BoundaryCoefficient α P level n +
        mtC2Coefficient α lowerSpill upperSpill level n := by
  let f : ℕ → ℂ := fun q => if q ∣ n then
    ∑ m ∈ (n / q).divisors, α m * (rho ((n / q) / m) (level q) : ℂ)
    else 0
  have hunion := Finset.sum_union hdisj (f := f)
  have hsdiff := Finset.sum_sdiff hlower (f := f)
  unfold mtC2Coefficient mtC2BoundaryCoefficient
  dsimp [f] at hunion hsdiff ⊢
  rw [hunion, ← hsdiff]
  ring

/-- Replacing the clipped prime's sifting level `q` by its block bottom is exactly `c₃,n`. -/
theorem mtC3Coefficient_eq_boundary_sub
    (α : ℕ → ℂ) (P : Finset ℕ) (lower : ℕ → ℕ) (n : ℕ) :
    mtC3Coefficient α P lower n =
      mtC2BoundaryCoefficient α P lower n -
        mtC2BoundaryCoefficient α P id n := by
  unfold mtC3Coefficient mtC2BoundaryCoefficient
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  split_ifs with hqn
  · rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    simp only [id_eq, mul_sub]
  · ring

/-- Literal complex-valued identity in Matomäki--Teräväinen Lemma 2.3(i), equation (2.12). -/
theorem matomakiTeravainen_lemma23i_exact
    (α : ℕ → ℂ) {n z₀ z₁ D : ℕ} (hn : 0 < n) (hz : z₀ ≤ z₁)
    (lowerSpill upperSpill : Finset ℕ) (lower : ℕ → ℕ)
    (hlower : lowerSpill ⊆ primesIco z₀ z₁)
    (hdisj : Disjoint (primesIco z₀ z₁ \ lowerSpill) upperSpill) :
    (∑ m ∈ n.divisors, α m * (rho (n / m) z₁ : ℂ)) =
      (∑ m ∈ n.divisors, α m * (truncLegendre (n / m) z₀ D : ℂ)) -
        mtC2BoundaryCoefficient α
          ((primesIco z₀ z₁ \ lowerSpill) ∪ upperSpill) lower n +
        (mtC1Coefficient α z₀ D n +
          mtC2Coefficient α lowerSpill upperSpill lower n +
          mtC3Coefficient α (primesIco z₀ z₁) lower n) := by
  have hbase := buchstab_c1_decomposition α (D := D) hn hz
  have hc2 := mtC2Boundary_main_eq_clipped_add_mtC2 α
    (primesIco z₀ z₁) lowerSpill upperSpill lower n hlower hdisj
  have hc3 := mtC3Coefficient_eq_boundary_sub α (primesIco z₀ z₁) lower n
  rw [hbase, hc2, hc3]
  ring

/-! ## Pointwise size needed to pass from the weighted first moment to the source mean square -/

/-- The literal truncation error has at most one ternary factorization per discarded divisor. -/
theorem norm_mtC1Coefficient_le_ternaryDivisorCount
    (α : ℕ → ℂ) {z D n : ℕ} (hn : 0 < n)
    {B : ℝ} (hB : 0 ≤ B) (hα : ∀ m, ‖α m‖ ≤ B) :
    ‖mtC1Coefficient α z D n‖ ≤ B * (ternaryDivisorCount n : ℝ) := by
  unfold mtC1Coefficient ternaryDivisorCount
  calc
    ‖∑ m ∈ n.divisors,
        α m * ((rho (n / m) z : ℂ) - (truncLegendre (n / m) z D : ℂ))‖ ≤
      ∑ m ∈ n.divisors,
        ‖α m * ((rho (n / m) z : ℂ) - (truncLegendre (n / m) z D : ℂ))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ m ∈ n.divisors, B * (((n / m).divisors.card : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro m hm
      have hmDvd : m ∣ n := (Nat.mem_divisors.mp hm).1
      have hk : 0 < n / m :=
        Nat.div_pos (Nat.le_of_dvd hn hmDvd) (Nat.pos_of_mem_divisors hm)
      have hnorm :
          ‖(rho (n / m) z : ℂ) - (truncLegendre (n / m) z D : ℂ)‖ ≤
            (truncTail (n / m) z D : ℝ) := by
        rw [← Int.cast_natCast, ← Int.cast_sub, Complex.norm_intCast]
        exact_mod_cast abs_rho_sub_truncLegendre_le hk
      have htailNat : truncTail (n / m) z D ≤ (n / m).divisors.card := by
        unfold truncTail
        calc
          ((Nat.gcd (n / m) (siftModulus z)).divisors.filter
              (fun e => ¬e ≤ D)).card ≤
              (Nat.gcd (n / m) (siftModulus z)).divisors.card :=
            Finset.card_filter_le _ _
          _ ≤ (n / m).divisors.card :=
            card_divisors_mono_of_dvd (Nat.gcd_dvd_left _ _) hk.ne'
      rw [norm_mul]
      exact mul_le_mul (hα m) (hnorm.trans (by exact_mod_cast htailNat))
        (norm_nonneg _) hB
    _ = B * ∑ m ∈ n.divisors, ((n / m).divisors.card : ℝ) := by
      rw [Finset.mul_sum]
  push_cast
  exact le_rfl

/-- One prime-first boundary coefficient has at most the ternary divisor multiplicity. -/
theorem norm_mtC2BoundaryCoefficient_le_ternaryDivisorCount
    (α : ℕ → ℂ) (S : Finset ℕ) (level : ℕ → ℕ) {n : ℕ} (hn : 0 < n)
    {B : ℝ} (hB : 0 ≤ B) (hα : ∀ m, ‖α m‖ ≤ B) :
    ‖mtC2BoundaryCoefficient α S level n‖ ≤
      B * (ternaryDivisorCount n : ℝ) := by
  unfold mtC2BoundaryCoefficient ternaryDivisorCount
  calc
    ‖∑ q ∈ S, if q ∣ n then
        ∑ m ∈ (n / q).divisors,
          α m * (rho ((n / q) / m) (level q) : ℂ) else 0‖ ≤
      ∑ q ∈ S, ‖if q ∣ n then
        ∑ m ∈ (n / q).divisors,
          α m * (rho ((n / q) / m) (level q) : ℂ) else 0‖ :=
      norm_sum_le _ _
    _ ≤ ∑ q ∈ S, if q ∣ n then B * ((n / q).divisors.card : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro q hq
      split_ifs with hqn
      · calc
          ‖∑ m ∈ (n / q).divisors,
              α m * (rho ((n / q) / m) (level q) : ℂ)‖ ≤
            ∑ m ∈ (n / q).divisors,
              ‖α m * (rho ((n / q) / m) (level q) : ℂ)‖ := norm_sum_le _ _
          _ ≤ ∑ _m ∈ (n / q).divisors, B := by
            apply Finset.sum_le_sum
            intro m hm
            rw [norm_mul]
            have hrho : ‖(rho ((n / q) / m) (level q) : ℂ)‖ ≤ 1 := by
              exact_mod_cast rho_le_one ((n / q) / m) (level q)
            simpa using mul_le_mul (hα m) hrho (norm_nonneg _) hB
          _ = B * ((n / q).divisors.card : ℝ) := by
            simp [Finset.sum_const, nsmul_eq_mul]
            ring
      · simp
    _ = ∑ q ∈ n.divisors,
        if q ∈ S then B * ((n / q).divisors.card : ℝ) else 0 := by
      rw [sum_divisors_indicator_eq_sum_finset_dvd hn]
    _ ≤ ∑ q ∈ n.divisors, B * ((n / q).divisors.card : ℝ) := by
      apply Finset.sum_le_sum
      intro q hq
      split_ifs
      · exact le_rfl
      · positivity
    _ = B * ∑ q ∈ n.divisors, ((n / q).divisors.card : ℝ) := by
      rw [Finset.mul_sum]
  push_cast
  exact le_rfl

/-- The two signed endpoint families cost at most twice the ternary divisor multiplicity. -/
theorem norm_mtC2Coefficient_le_two_mul_ternaryDivisorCount
    (α : ℕ → ℂ) (lowerSpill upperSpill : Finset ℕ) (level : ℕ → ℕ)
    {n : ℕ} (hn : 0 < n) {B : ℝ} (hB : 0 ≤ B) (hα : ∀ m, ‖α m‖ ≤ B) :
    ‖mtC2Coefficient α lowerSpill upperSpill level n‖ ≤
      2 * B * (ternaryDivisorCount n : ℝ) := by
  unfold mtC2Coefficient
  calc
    ‖mtC2BoundaryCoefficient α upperSpill level n -
        mtC2BoundaryCoefficient α lowerSpill level n‖ ≤
      ‖mtC2BoundaryCoefficient α upperSpill level n‖ +
        ‖mtC2BoundaryCoefficient α lowerSpill level n‖ := norm_sub_le _ _
    _ ≤ B * (ternaryDivisorCount n : ℝ) +
        B * (ternaryDivisorCount n : ℝ) := by
      gcongr
      · exact norm_mtC2BoundaryCoefficient_le_ternaryDivisorCount
          α upperSpill level hn hB hα
      · exact norm_mtC2BoundaryCoefficient_le_ternaryDivisorCount
          α lowerSpill level hn hB hα
    _ = 2 * B * (ternaryDivisorCount n : ℝ) := by ring

/-- The block-level replacement error costs at most twice the ternary divisor multiplicity. -/
theorem norm_mtC3Coefficient_le_two_mul_ternaryDivisorCount
    (α : ℕ → ℂ) (S : Finset ℕ) (lower : ℕ → ℕ)
    {n : ℕ} (hn : 0 < n) {B : ℝ} (hB : 0 ≤ B) (hα : ∀ m, ‖α m‖ ≤ B) :
    ‖mtC3Coefficient α S lower n‖ ≤
      2 * B * (ternaryDivisorCount n : ℝ) := by
  rw [mtC3Coefficient_eq_boundary_sub]
  calc
    ‖mtC2BoundaryCoefficient α S lower n - mtC2BoundaryCoefficient α S id n‖ ≤
      ‖mtC2BoundaryCoefficient α S lower n‖ +
        ‖mtC2BoundaryCoefficient α S id n‖ := norm_sub_le _ _
    _ ≤ B * (ternaryDivisorCount n : ℝ) +
        B * (ternaryDivisorCount n : ℝ) := by
      gcongr
      · exact norm_mtC2BoundaryCoefficient_le_ternaryDivisorCount α S lower hn hB hα
      · exact norm_mtC2BoundaryCoefficient_le_ternaryDivisorCount α S id hn hB hα
    _ = 2 * B * (ternaryDivisorCount n : ℝ) := by ring

/-- Literal combined error `c₁,n + c₂,n + c₃,n`. -/
def mtLemma23Error
    (α : ℕ → ℂ) (z D : ℕ) (lowerSpill upperSpill P : Finset ℕ)
    (lower : ℕ → ℕ) (n : ℕ) : ℂ :=
  mtC1Coefficient α z D n +
    mtC2Coefficient α lowerSpill upperSpill lower n +
    mtC3Coefficient α P lower n

/-- The combined source error is pointwise bounded by five ternary divisor counts. -/
theorem norm_mtLemma23Error_le_five_mul_ternaryDivisorCount
    (α : ℕ → ℂ) (z D : ℕ) (lowerSpill upperSpill P : Finset ℕ)
    (lower : ℕ → ℕ) {n : ℕ} (hn : 0 < n)
    {B : ℝ} (hB : 0 ≤ B) (hα : ∀ m, ‖α m‖ ≤ B) :
    ‖mtLemma23Error α z D lowerSpill upperSpill P lower n‖ ≤
      5 * B * (ternaryDivisorCount n : ℝ) := by
  unfold mtLemma23Error
  calc
    ‖mtC1Coefficient α z D n +
        mtC2Coefficient α lowerSpill upperSpill lower n +
        mtC3Coefficient α P lower n‖ ≤
      ‖mtC1Coefficient α z D n‖ +
          ‖mtC2Coefficient α lowerSpill upperSpill lower n‖ +
        ‖mtC3Coefficient α P lower n‖ := by
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ B * (ternaryDivisorCount n : ℝ) +
          2 * B * (ternaryDivisorCount n : ℝ) +
        2 * B * (ternaryDivisorCount n : ℝ) := by
      gcongr
      · exact norm_mtC1Coefficient_le_ternaryDivisorCount α hn hB hα
      · exact norm_mtC2Coefficient_le_two_mul_ternaryDivisorCount α
          lowerSpill upperSpill lower hn hB hα
      · exact norm_mtC3Coefficient_le_two_mul_ternaryDivisorCount α P lower hn hB hα
    _ = 5 * B * (ternaryDivisorCount n : ℝ) := by ring

end

end RHTower.Sieve
