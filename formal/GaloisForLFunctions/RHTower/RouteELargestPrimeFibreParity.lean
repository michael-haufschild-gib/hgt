import GaloisForLFunctions.RHTower.RouteEPrimitiveAllGradeParityBarrier

open Finset

namespace RHTower

private theorem routeEPrimitive_scaled_remainder_bound
    {a d q : ℝ} (ha : 0 ≤ a) (hd : 0 < d) (hq : 0 < q) :
    0 ≤ a / d ^ (2 : ℕ) -
        q ^ (2 : ℕ) * routeEPrimitiveConeWeight a (q * d) ∧
      a / d ^ (2 : ℕ) -
        q ^ (2 : ℕ) * routeEPrimitiveConeWeight a (q * d) ≤
          3 * a ^ (2 : ℕ) / (q * d ^ (3 : ℕ)) := by
  have hqd : 0 < q * d := mul_pos hq hd
  have h₁ : 0 < a + q * d := by linarith
  have h₂ : 0 < 2 * a + q * d := by linarith
  have hden : 0 < d ^ (2 : ℕ) * ((a + q * d) * (2 * a + q * d)) := by positivity
  have hqd3 : 0 < q * d ^ (3 : ℕ) := by positivity
  have hdiff :
      a / d ^ (2 : ℕ) -
          q ^ (2 : ℕ) * routeEPrimitiveConeWeight a (q * d) =
        a ^ (2 : ℕ) * (2 * a + 3 * q * d) /
          (d ^ (2 : ℕ) * ((a + q * d) * (2 * a + q * d))) := by
    unfold routeEPrimitiveConeWeight
    field_simp
    ring
  constructor
  · rw [hdiff]
    positivity
  · rw [hdiff]
    apply (div_le_div_iff₀ hden hqd3).2
    have hkey : q * d * (2 * a + 3 * q * d) ≤
        3 * ((a + q * d) * (2 * a + q * d)) := by
      nlinarith [sq_nonneg a, mul_nonneg ha hqd.le]
    have hmul := mul_le_mul_of_nonneg_left hkey
      (mul_nonneg (sq_nonneg a) (sq_nonneg d))
    nlinarith [hmul]

private noncomputable def lpfFactor (n : ℕ) : ℝ := 1 - 1 / (n : ℝ) ^ (2 : ℕ)

private theorem lpfFactor_pos {n : ℕ} (hn : 2 ≤ n) : 0 < lpfFactor n := by
  unfold lpfFactor
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  rw [sub_pos, div_lt_one (by positivity)]
  nlinarith

private theorem lpfFactor_le_one (n : ℕ) : lpfFactor n ≤ 1 := by
  unfold lpfFactor
  have hnonneg : 0 ≤ 1 / (n : ℝ) ^ (2 : ℕ) := by positivity
  linarith

private theorem lpfProd_Icc_eq {n : ℕ} (hn : 2 ≤ n) :
    (∏ i ∈ Finset.Icc 2 n, lpfFactor i) =
      ((n : ℝ) + 1) / (2 * (n : ℝ)) := by
  induction n, hn using Nat.le_induction with
  | base =>
      norm_num [lpfFactor]
  | succ m hm ih =>
      rw [Finset.prod_Icc_succ_top (by omega) lpfFactor, ih]
      unfold lpfFactor
      have hmR : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hm)
      have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by linarith
      push_cast
      field_simp
      ring

private noncomputable def lpfU (R : Finset Nat.Primes) : ℝ :=
  ∏ p ∈ R, lpfFactor p

private theorem lpfU_ge_half (R : Finset Nat.Primes) {q : ℕ}
    (hq : 3 ≤ q) (hR : ∀ p ∈ R, (p : ℕ) < q) :
    (1 / 2 : ℝ) ≤ lpfU R := by
  classical
  let S : Finset ℕ := R.image (fun p : Nat.Primes => (p : ℕ))
  have hS : S ⊆ Finset.Icc 2 (q - 1) := by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hn
    have hpq := hR p hp
    exact Finset.mem_Icc.mpr ⟨p.property.two_le, by omega⟩
  have hprod :
      (∏ n ∈ S, lpfFactor n) = lpfU R := by
    dsimp [S, lpfU]
    rw [Finset.prod_image]
    intro p hp r hr h
    exact Subtype.ext h
  have htotal :
      (∏ n ∈ Finset.Icc 2 (q - 1), lpfFactor n) =
        (q : ℝ) / (2 * ((q : ℝ) - 1)) := by
    have hq1 : 2 ≤ q - 1 := by omega
    rw [lpfProd_Icc_eq hq1]
    have hcast : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
      exact_mod_cast Nat.cast_sub (by omega : 1 ≤ q)
    rw [hcast]
    ring
  have hsubset :
      (∏ n ∈ Finset.Icc 2 (q - 1), lpfFactor n) ≤
        ∏ n ∈ S, lpfFactor n := by
    exact Finset.prod_le_prod_of_subset_of_le_one hS
      (fun n hn => (lpfFactor_pos (Finset.mem_Icc.mp hn).1).le)
      (fun n hn hns => lpfFactor_le_one n)
  rw [htotal, hprod] at hsubset
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast (le_trans (by omega : 2 ≤ 3) hq)
  have hq1pos : 0 < (q : ℝ) - 1 := by linarith
  have hhalf : (1 / 2 : ℝ) ≤ (q : ℝ) / (2 * ((q : ℝ) - 1)) := by
    apply (le_div_iff₀ (by positivity)).2
    linarith
  exact hhalf.trans hsubset

private theorem lpfU_pos (R : Finset Nat.Primes) : 0 < lpfU R := by
  unfold lpfU
  apply Finset.prod_pos
  intro p hp
  exact lpfFactor_pos p.property.two_le

private theorem lpfSumSq (P : Finset Nat.Primes) :
    (∑ S ∈ P.powerset, (∏ p ∈ S, (p : ℝ)) ^ (2 : ℕ)) =
      ∏ p ∈ P, (1 + (p : ℝ) ^ (2 : ℕ)) := by
  rw [Finset.prod_one_add]
  apply Finset.sum_congr rfl
  intro S hS
  rw [Finset.prod_pow]

private theorem lpfDisjointBooleanExpansion
    (P R : Finset Nat.Primes) (hPR : P ⊆ R)
    (x y : Nat.Primes → ℝ) :
    (∑ D ∈ R.powerset, (∏ r ∈ D, y r) *
      ∑ S ∈ P.powerset, if Disjoint S D then ∏ p ∈ S, x p else 0) =
      (∏ p ∈ P, (1 + x p + y p)) *
        ∏ r ∈ R \ P, (1 + y r) := by
  classical
  have hinner (D : Finset Nat.Primes) :
      (∑ S ∈ P.powerset, if Disjoint S D then ∏ p ∈ S, x p else 0) =
        ∏ p ∈ P \ D, (1 + x p) := by
    have hfilter :
        (P.powerset.filter fun S => Disjoint S D) = (P \ D).powerset := by
      ext S
      simp only [Finset.mem_filter, Finset.mem_powerset]
      exact Finset.subset_sdiff.symm
    rw [Finset.prod_one_add, ← hfilter, Finset.sum_filter]
  let g : Nat.Primes → ℝ := fun r => if r ∈ P then 1 + x r else 1
  have hcomplement (D : Finset Nat.Primes) :
      (∏ r ∈ R \ D, g r) = ∏ p ∈ P \ D, (1 + x p) := by
    have hsub : P \ D ⊆ R \ D := Finset.sdiff_subset_sdiff_left D hPR
    calc
      (∏ r ∈ R \ D, g r) = ∏ p ∈ P \ D, g p := by
        symm
        apply Finset.prod_subset hsub
        intro r hr hnot
        have hrP : r ∉ P := by
          intro hp
          exact hnot (Finset.mem_sdiff.mpr ⟨hp, (Finset.mem_sdiff.mp hr).2⟩)
        simp [g, hrP]
      _ = ∏ p ∈ P \ D, (1 + x p) := by
        apply Finset.prod_congr rfl
        intro p hp
        simp [g, (Finset.mem_sdiff.mp hp).1]
  have hsplit :
      (∏ r ∈ R, (y r + g r)) =
        (∏ p ∈ P, (1 + x p + y p)) *
          ∏ r ∈ R \ P, (1 + y r) := by
    calc
      (∏ r ∈ R, (y r + g r)) =
          ∏ r ∈ P ∪ (R \ P), (y r + g r) := by
            rw [Finset.union_sdiff_of_subset hPR]
      _ = (∏ p ∈ P, (y p + g p)) * ∏ r ∈ R \ P, (y r + g r) := by
            rw [Finset.prod_union Finset.disjoint_sdiff]
      _ = (∏ p ∈ P, (1 + x p + y p)) *
            ∏ r ∈ R \ P, (1 + y r) := by
            congr 1
            · apply Finset.prod_congr rfl
              intro p hp
              simp [g, hp, add_comm, add_left_comm]
            · apply Finset.prod_congr rfl
              intro r hr
              have hrP := (Finset.mem_sdiff.mp hr).2
              simp [g, hrP, add_comm]
  calc
    (∑ D ∈ R.powerset, (∏ r ∈ D, y r) *
      ∑ S ∈ P.powerset, if Disjoint S D then ∏ p ∈ S, x p else 0) =
        ∑ D ∈ R.powerset, (∏ r ∈ D, y r) *
          ∏ p ∈ P \ D, (1 + x p) := by
            apply Finset.sum_congr rfl
            intro D hD
            rw [hinner]
    _ = ∑ D ∈ R.powerset, (∏ r ∈ D, y r) *
          ∏ r ∈ R \ D, g r := by
            apply Finset.sum_congr rfl
            intro D hD
            rw [hcomplement]
    _ = ∏ r ∈ R, (y r + g r) := (Finset.prod_add y g R).symm
    _ = _ := hsplit

private noncomputable def lpfMain (P R : Finset Nat.Primes) : ℝ :=
  -(∏ p ∈ P, (1 - (p : ℝ) - 1 / (p : ℝ) ^ (2 : ℕ))) *
    lpfU (R \ P)

/-- Exact parity margin after removing numerator primes from the denominator
Euler product. Its local factors grow linearly with each prime. -/
noncomputable def routeELargestPrimeParityMargin (P : Finset Nat.Primes) : ℝ :=
  ∏ p ∈ P, ((p : ℝ) + 1 / (p : ℝ) ^ (2 : ℕ) - 1)

private theorem lpfC_one_le (P : Finset Nat.Primes) :
    1 ≤ routeELargestPrimeParityMargin P := by
  unfold routeELargestPrimeParityMargin
  apply Finset.one_le_prod
  intro p hp
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast p.property.two_le
  have hnonneg : 0 ≤ 1 / (p : ℝ) ^ (2 : ℕ) := by positivity
  linarith

private theorem lpfMain_sign (P R : Finset Nat.Primes) {q : ℕ}
    (hq : 3 ≤ q) (hR : ∀ p ∈ R, (p : ℕ) < q) :
    (1 / 2 : ℝ) * routeELargestPrimeParityMargin P ≤
      (-1 : ℝ) ^ (P.card + 1) * lpfMain P R := by
  have hU : (1 / 2 : ℝ) ≤ lpfU (R \ P) :=
    lpfU_ge_half (R \ P) hq (by
      intro p hp
      exact hR p (Finset.mem_sdiff.mp hp).1)
  have hprod := lpfC_one_le P
  have hneg :
      (-1 : ℝ) ^ P.card *
        (∏ p ∈ P, (1 - (p : ℝ) - 1 / (p : ℝ) ^ (2 : ℕ))) =
      ∏ p ∈ P, ((p : ℝ) + 1 / (p : ℝ) ^ (2 : ℕ) - 1) := by
    rw [← Finset.prod_neg]
    apply Finset.prod_congr rfl
    intro p hp
    ring
  have hval :
      (-1 : ℝ) ^ (P.card + 1) * lpfMain P R =
        (∏ p ∈ P, ((p : ℝ) + 1 / (p : ℝ) ^ (2 : ℕ) - 1)) *
          lpfU (R \ P) := by
    calc
      (-1 : ℝ) ^ (P.card + 1) * lpfMain P R =
          ((-1 : ℝ) ^ P.card *
            ∏ p ∈ P, (1 - (p : ℝ) - 1 / (p : ℝ) ^ (2 : ℕ))) *
              lpfU (R \ P) := by
            unfold lpfMain
            rw [pow_succ]
            ring
      _ = _ := by rw [hneg]
  rw [hval]
  change (1 / 2 : ℝ) * (∏ p ∈ P,
      ((p : ℝ) + 1 / (p : ℝ) ^ (2 : ℕ) - 1)) ≤ _
  have hprod0 : 0 ≤ ∏ p ∈ P,
      ((p : ℝ) + 1 / (p : ℝ) ^ (2 : ℕ) - 1) := by
    change 1 ≤ (∏ p ∈ P,
      ((p : ℝ) + 1 / (p : ℝ) ^ (2 : ℕ) - 1)) at hprod
    linarith
  simpa only [mul_comm] using
    (mul_le_mul_of_nonneg_left hU hprod0)

private noncomputable def lpfNumeratorWeight (p : Nat.Primes) : ℝ := -(p : ℝ)

private noncomputable def lpfDenominatorWeight (p : Nat.Primes) : ℝ :=
  -(1 / (p : ℝ) ^ (2 : ℕ))

private theorem lpfMain_eq_disjointBoolean (P R : Finset Nat.Primes)
    (hPR : P ⊆ R) :
    lpfMain P R =
      -∑ D ∈ R.powerset, (∏ r ∈ D, lpfDenominatorWeight r) *
        ∑ S ∈ P.powerset,
          if Disjoint S D then ∏ p ∈ S, lpfNumeratorWeight p else 0 := by
  rw [lpfDisjointBooleanExpansion P R hPR]
  simp only [lpfMain, lpfU, lpfFactor, lpfNumeratorWeight,
    lpfDenominatorWeight, sub_eq_add_neg]
  ring

private def lpfNatProd (S : Finset Nat.Primes) : ℕ := ∏ p ∈ S, (p : ℕ)

private noncomputable def lpfRealProd (S : Finset Nat.Primes) : ℝ :=
  ∏ p ∈ S, (p : ℝ)

private theorem lpfNatProd_cast (S : Finset Nat.Primes) :
    (lpfNatProd S : ℝ) = lpfRealProd S := by
  simp [lpfNatProd, lpfRealProd]

private theorem lpfRealProd_pos (S : Finset Nat.Primes) :
    0 < lpfRealProd S := by
  unfold lpfRealProd
  apply Finset.prod_pos
  intro p hp
  exact_mod_cast p.property.pos

private theorem lpfNumeratorWeight_prod (S : Finset Nat.Primes) :
    (∏ p ∈ S, lpfNumeratorWeight p) =
      (-1 : ℝ) ^ S.card * lpfRealProd S := by
  simpa only [lpfNumeratorWeight, lpfRealProd] using
    (Finset.prod_neg (s := S) (f := fun p : Nat.Primes => (p : ℝ)))

private theorem lpfDenominatorWeight_prod (D : Finset Nat.Primes) :
    (∏ p ∈ D, lpfDenominatorWeight p) =
      (-1 : ℝ) ^ D.card / lpfRealProd D ^ (2 : ℕ) := by
  have hneg := Finset.prod_neg (s := D)
    (f := fun p : Nat.Primes => 1 / (p : ℝ) ^ (2 : ℕ))
  have hinv :
      (∏ p ∈ D, 1 / (p : ℝ) ^ (2 : ℕ)) =
        1 / lpfRealProd D ^ (2 : ℕ) := by
    simp [lpfRealProd, Finset.prod_pow]
  unfold lpfDenominatorWeight
  rw [hneg, hinv]
  ring

private theorem lpfNatProd_injOn (R : Finset Nat.Primes) :
    Set.InjOn lpfNatProd (R.powerset : Set (Finset Nat.Primes)) := by
  classical
  have key : ∀ A B : Finset Nat.Primes, A ⊆ R → B ⊆ R →
      lpfNatProd A = lpfNatProd B → ∀ p ∈ A, p ∈ B := by
    intro A B hA hB hprod p hp
    have hdiv : (p : ℕ) ∣ ∏ r ∈ B, (r : ℕ) := by
      change (p : ℕ) ∣ lpfNatProd B
      rw [← hprod]
      change (p : ℕ) ∣ ∏ r ∈ A, (r : ℕ)
      exact Finset.dvd_prod_of_mem (fun r : Nat.Primes => (r : ℕ)) hp
    obtain ⟨r, hr, hpr⟩ :=
      ((Nat.Prime.prime p.property).dvd_finsetProd_iff _).mp hdiv
    have hEq : p = r := Subtype.ext
      ((Nat.prime_dvd_prime_iff_eq p.property r.property).mp hpr)
    simpa [hEq] using hr
  intro A hA B hB hprod
  have hAR := Finset.mem_powerset.mp hA
  have hBR := Finset.mem_powerset.mp hB
  ext p
  exact ⟨key A B hAR hBR hprod p, key B A hBR hAR hprod.symm p⟩

private theorem lpfNatProd_le (R D : Finset Nat.Primes) (hDR : D ⊆ R) :
    lpfNatProd D ≤ lpfNatProd R := by
  unfold lpfNatProd
  exact Finset.prod_le_prod_of_subset_of_one_le' hDR
    (fun p hp hnot => p.property.one_le)

private theorem lpfNatProd_pos (D : Finset Nat.Primes) : 0 < lpfNatProd D := by
  unfold lpfNatProd
  exact Finset.prod_pos (fun p hp => p.property.pos)

private theorem lpfFull_sq_le_two (R : Finset Nat.Primes) :
    (∑ D ∈ R.powerset, 1 / (lpfNatProd D : ℝ) ^ (2 : ℕ)) ≤ 2 := by
  classical
  let V := R.powerset.image lpfNatProd
  have hV : V ⊆ Finset.Ioo 0 (lpfNatProd R + 1) := by
    intro d hd
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hd
    exact Finset.mem_Ioo.mpr ⟨lpfNatProd_pos D,
      Nat.lt_succ_of_le (lpfNatProd_le R D (Finset.mem_powerset.mp hD))⟩
  have hI : (∑ d ∈ V, 1 / (d : ℝ) ^ (2 : ℕ)) ≤
      ∑ d ∈ Finset.Ioo 0 (lpfNatProd R + 1), 1 / (d : ℝ) ^ (2 : ℕ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hV
    intro d hd hnot
    positivity
  calc
    (∑ D ∈ R.powerset, 1 / (lpfNatProd D : ℝ) ^ (2 : ℕ)) =
        ∑ d ∈ V, 1 / (d : ℝ) ^ (2 : ℕ) := by
          rw [Finset.sum_image]
          intro D hD E hE hEq
          exact lpfNatProd_injOn R hD hE hEq
    _ ≤ ∑ d ∈ Finset.Ioo 0 (lpfNatProd R + 1),
          1 / (d : ℝ) ^ (2 : ℕ) := hI
    _ ≤ 2 := by
      have h := sum_Ioo_inv_sq_le (α := ℝ) 0 (lpfNatProd R + 1)
      norm_num at h ⊢
      simpa only [one_div] using h

private theorem lpfRealProd_one_le (D : Finset Nat.Primes) :
    1 ≤ lpfRealProd D := by
  have h := lpfNatProd_pos D
  rw [← lpfNatProd_cast]
  exact_mod_cast h

private theorem lpfSumSq_le (P : Finset Nat.Primes) :
    (∑ S ∈ P.powerset, lpfRealProd S) ≤
      ∏ p ∈ P, (1 + (p : ℝ) ^ (2 : ℕ)) := by
  rw [← lpfSumSq]
  apply Finset.sum_le_sum
  intro S hS
  have h := lpfRealProd_one_le S
  dsimp [lpfRealProd] at h ⊢
  nlinarith [sq_nonneg (lpfRealProd S)]

private theorem lpfTail_sq_le (R : Finset Nat.Primes) {q : ℕ} (hq : 2 ≤ q) :
    (∑ D ∈ R.powerset,
      if q ≤ lpfNatProd D then 1 / (lpfNatProd D : ℝ) ^ (2 : ℕ) else 0) ≤
        1 / ((q : ℝ) - 1) := by
  classical
  let T := R.powerset.filter (fun D => q ≤ lpfNatProd D)
  let V := T.image lpfNatProd
  let N := max (q - 1) (lpfNatProd R)
  have hV : V ⊆ Finset.Ioc (q - 1) N := by
    intro d hd
    obtain ⟨D, hDT, rfl⟩ := Finset.mem_image.mp hd
    have hD := Finset.mem_filter.mp hDT
    exact Finset.mem_Ioc.mpr ⟨by omega,
      (lpfNatProd_le R D (Finset.mem_powerset.mp hD.1)).trans (le_max_right _ _)⟩
  have hI : (∑ d ∈ V, 1 / (d : ℝ) ^ (2 : ℕ)) ≤
      ∑ d ∈ Finset.Ioc (q - 1) N, 1 / (d : ℝ) ^ (2 : ℕ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hV
    intro d hd hnot
    positivity
  have hsum : (∑ d ∈ Finset.Ioc (q - 1) N,
      1 / (d : ℝ) ^ (2 : ℕ)) ≤ 1 / ((q : ℝ) - 1) := by
    have hseries := sum_Ioc_inv_sq_le_sub (α := ℝ)
      (k := q - 1) (n := N) (by omega) (le_max_left _ _)
    have hcast : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
      exact_mod_cast Nat.cast_sub (by omega : 1 ≤ q)
    have hseries' : (∑ d ∈ Finset.Ioc (q - 1) N,
        1 / (d : ℝ) ^ (2 : ℕ)) ≤
          1 / ((q : ℝ) - 1) - (N : ℝ)⁻¹ := by
      simpa only [one_div, hcast] using hseries
    have hnonneg : 0 ≤ (N : ℝ)⁻¹ := by positivity
    linarith
  calc
    (∑ D ∈ R.powerset,
      if q ≤ lpfNatProd D then 1 / (lpfNatProd D : ℝ) ^ (2 : ℕ) else 0) =
        ∑ D ∈ T, 1 / (lpfNatProd D : ℝ) ^ (2 : ℕ) := by
          simp [T, Finset.sum_filter]
    _ = ∑ d ∈ V, 1 / (d : ℝ) ^ (2 : ℕ) := by
      rw [Finset.sum_image]
      intro D hD E hE hEq
      exact lpfNatProd_injOn R
        (Finset.mem_filter.mp hD).1
        (Finset.mem_filter.mp hE).1 hEq
    _ ≤ _ := hI.trans hsum

private theorem lpfAbs_double_sum_le {α β : Type*} (A : Finset α) (B : Finset β)
    (f g : α → β → ℝ) (h : ∀ a ∈ A, ∀ b ∈ B, |f a b| ≤ g a b) :
    |∑ a ∈ A, ∑ b ∈ B, f a b| ≤ ∑ a ∈ A, ∑ b ∈ B, g a b := by
  calc
    |∑ a ∈ A, ∑ b ∈ B, f a b| ≤
        ∑ a ∈ A, |∑ b ∈ B, f a b| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ A, ∑ b ∈ B, |f a b| := by
      apply Finset.sum_le_sum
      intro a ha
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ A, ∑ b ∈ B, g a b := by
      apply Finset.sum_le_sum
      intro a ha
      exact Finset.sum_le_sum (h a ha)

private noncomputable def lpfCoeff (S D : Finset Nat.Primes) : ℝ :=
  (-1 : ℝ) ^ (S.card + D.card + 1)

private theorem lpfCoeff_abs (S D : Finset Nat.Primes) :
    |lpfCoeff S D| = 1 := by
  simp [lpfCoeff]

private theorem lpfMobius_prod (S : Finset Nat.Primes) :
    (ArithmeticFunction.moebius (lpfNatProd S) : ℝ) =
      (-1 : ℝ) ^ S.card := by
  let T : Finset ℕ := S.image (fun p : Nat.Primes => (p : ℕ))
  have hT : ∀ p ∈ T, p.Prime := by
    intro p hp
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hp
    exact r.property
  have hcard : T.card = S.card :=
    Finset.card_image_of_injective S Subtype.val_injective
  have hprod : (∏ p ∈ T, p) = lpfNatProd S := by
    dsimp [T, lpfNatProd]
    rw [Finset.prod_image]
    intro p hp r hr hpr
    exact Subtype.ext hpr
  have hmu := GibbsGas.moebius_prod_primes hT
  rw [hprod, hcard] at hmu
  exact_mod_cast hmu

private theorem lpfCoeff_eq_mobius (S D : Finset Nat.Primes)
    (q : Nat.Primes) (hD : ∀ r ∈ D, (r : ℕ) < (q : ℕ)) :
    lpfCoeff S D =
      (ArithmeticFunction.moebius (lpfNatProd S) : ℝ) *
        (ArithmeticFunction.moebius ((q : ℕ) * lpfNatProd D) : ℝ) := by
  have hqnot : q ∉ D := by
    intro hq
    exact (lt_irrefl (q : ℕ)) (hD q hq)
  have hqprod : lpfNatProd (insert q D) = (q : ℕ) * lpfNatProd D := by
    simp [lpfNatProd, hqnot]
  rw [← hqprod, lpfMobius_prod S, lpfMobius_prod (insert q D),
    Finset.card_insert_of_notMem hqnot]
  unfold lpfCoeff
  rw [pow_add, pow_succ]
  ring

private theorem lpfSigned_remainder_bound (S D : Finset Nat.Primes) {q : ℕ}
    (hq : 0 < q) :
    |lpfCoeff S D *
      ((q : ℝ) ^ (2 : ℕ) * routeEPrimitiveConeWeight
        (lpfRealProd S) ((q : ℝ) * lpfRealProd D) -
          lpfRealProd S / lpfRealProd D ^ (2 : ℕ))| ≤
        3 * lpfRealProd S ^ (2 : ℕ) /
          ((q : ℝ) * lpfRealProd D ^ (3 : ℕ)) := by
  have hrem := routeEPrimitive_scaled_remainder_bound
    (a := lpfRealProd S) (d := lpfRealProd D) (q := (q : ℝ))
    (lpfRealProd_pos S).le (lpfRealProd_pos D) (by exact_mod_cast hq)
  rw [abs_mul, lpfCoeff_abs, one_mul]
  have hneg : (q : ℝ) ^ (2 : ℕ) * routeEPrimitiveConeWeight
        (lpfRealProd S) ((q : ℝ) * lpfRealProd D) -
          lpfRealProd S / lpfRealProd D ^ (2 : ℕ) =
      -(lpfRealProd S / lpfRealProd D ^ (2 : ℕ) -
        (q : ℝ) ^ (2 : ℕ) * routeEPrimitiveConeWeight
          (lpfRealProd S) ((q : ℝ) * lpfRealProd D)) := by ring
  rw [hneg, abs_neg, abs_of_nonneg hrem.1]
  exact hrem.2

noncomputable def routeELargestPrimeQuadraticMass (P : Finset Nat.Primes) : ℝ :=
  ∏ p ∈ P, (1 + (p : ℝ) ^ (2 : ℕ))

private noncomputable abbrev lpfB (P : Finset Nat.Primes) : ℝ :=
  routeELargestPrimeQuadraticMass P

private theorem lpfB_pos (P : Finset Nat.Primes) : 0 < lpfB P := by
  unfold lpfB
  exact Finset.prod_pos (fun p hp => by positivity)

private theorem lpfWeighted_error_le (P R : Finset Nat.Primes) {q : ℕ}
    (hq : 0 < q) :
    (∑ D ∈ R.powerset, ∑ S ∈ P.powerset,
      3 * lpfRealProd S ^ (2 : ℕ) /
        ((q : ℝ) * lpfRealProd D ^ (3 : ℕ))) ≤
          6 * lpfB P / (q : ℝ) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hcubed (D : Finset Nat.Primes) :
      1 / lpfRealProd D ^ (3 : ℕ) ≤
        1 / lpfRealProd D ^ (2 : ℕ) := by
    have hd := lpfRealProd_one_le D
    have hd0 := lpfRealProd_pos D
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [sq_nonneg (lpfRealProd D - 1)]
  have hterm : (∑ D ∈ R.powerset, ∑ S ∈ P.powerset,
      3 * lpfRealProd S ^ (2 : ℕ) /
        ((q : ℝ) * lpfRealProd D ^ (3 : ℕ))) ≤
      ∑ D ∈ R.powerset, ∑ S ∈ P.powerset,
        3 * lpfRealProd S ^ (2 : ℕ) /
          ((q : ℝ) * lpfRealProd D ^ (2 : ℕ)) := by
    apply Finset.sum_le_sum
    intro D hD
    apply Finset.sum_le_sum
    intro S hS
    have h := hcubed D
    have hn : 0 ≤ 3 * lpfRealProd S ^ (2 : ℕ) / (q : ℝ) := by positivity
    have hmul := mul_le_mul_of_nonneg_left h hn
    convert hmul using 1 <;> ring
  have hfactor :
      (∑ D ∈ R.powerset, ∑ S ∈ P.powerset,
        3 * lpfRealProd S ^ (2 : ℕ) /
          ((q : ℝ) * lpfRealProd D ^ (2 : ℕ))) =
        (3 / (q : ℝ)) *
          (∑ S ∈ P.powerset, lpfRealProd S ^ (2 : ℕ)) *
            (∑ D ∈ R.powerset, 1 / lpfRealProd D ^ (2 : ℕ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro D hD
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro S hS
    ring
  calc
    _ ≤ _ := hterm
    _ = (3 / (q : ℝ)) * lpfB P *
        (∑ D ∈ R.powerset, 1 / lpfRealProd D ^ (2 : ℕ)) := by
          have hs : (∑ S ∈ P.powerset, lpfRealProd S ^ (2 : ℕ)) =
              lpfB P := by
            simpa only [lpfB, routeELargestPrimeQuadraticMass, lpfRealProd]
              using lpfSumSq P
          rw [hfactor, hs]
    _ ≤ (3 / (q : ℝ)) * lpfB P * 2 := by
      have hs : (∑ D ∈ R.powerset,
          1 / lpfRealProd D ^ (2 : ℕ)) ≤ 2 := by
        simpa only [← lpfNatProd_cast] using lpfFull_sq_le_two R
      have hnonneg : 0 ≤ (3 / (q : ℝ)) * lpfB P :=
        mul_nonneg (by positivity) (lpfB_pos P).le
      exact mul_le_mul_of_nonneg_left hs hnonneg
    _ = _ := by ring

/-- The complete largest-prime squarefree cofactor fibre, before its physical
cutoff. `D` records exactly the prime support of the denominator cofactor. -/
noncomputable def routeELargestPrimeFullFibre
    (P R : Finset Nat.Primes) (q : ℕ) : ℝ :=
  ∑ D ∈ R.powerset, ∑ S ∈ P.powerset,
    if Disjoint S D then
      lpfCoeff S D * routeEPrimitiveConeWeight
        (lpfRealProd S) ((q : ℝ) * lpfRealProd D)
    else 0

/-- The same literal squarefree fibre with the cutoff `d < q`. -/
noncomputable def routeELargestPrimeCutFibre
    (P R : Finset Nat.Primes) (q : ℕ) : ℝ :=
  ∑ D ∈ R.powerset, ∑ S ∈ P.powerset,
    if Disjoint S D ∧ lpfNatProd D < q then
      lpfCoeff S D * routeEPrimitiveConeWeight
        (lpfRealProd S) ((q : ℝ) * lpfRealProd D)
    else 0

/-- Literal arithmetic-function Möbius version of the complete squarefree
largest-prime cofactor fibre below the physical cutoff. -/
noncomputable def routeELargestPrimeMobiusFibre
    (P R : Finset Nat.Primes) (q : Nat.Primes) : ℝ :=
  ∑ D ∈ R.powerset, ∑ S ∈ P.powerset,
    if Disjoint S D ∧ lpfNatProd D < (q : ℕ) then
      (ArithmeticFunction.moebius (lpfNatProd S) : ℝ) *
        (ArithmeticFunction.moebius ((q : ℕ) * lpfNatProd D) : ℝ) *
          routeEPrimitiveConeWeight
            (lpfRealProd S) ((q : ℝ) * lpfRealProd D)
    else 0

theorem routeELargestPrimeMobiusFibre_eq_cut
    (P R : Finset Nat.Primes) (q : Nat.Primes)
    (hR : ∀ r ∈ R, (r : ℕ) < (q : ℕ)) :
    routeELargestPrimeMobiusFibre P R q =
      routeELargestPrimeCutFibre P R q := by
  unfold routeELargestPrimeMobiusFibre routeELargestPrimeCutFibre
  apply Finset.sum_congr rfl
  intro D hD
  apply Finset.sum_congr rfl
  intro S hS
  split_ifs with hdisj
  · rw [lpfCoeff_eq_mobius S D q (by
        intro r hr
        exact hR r ((Finset.mem_powerset.mp hD) hr))]
  · rfl

private noncomputable def lpfApprox (P R : Finset Nat.Primes) : ℝ :=
  ∑ D ∈ R.powerset, ∑ S ∈ P.powerset,
    if Disjoint S D then
      lpfCoeff S D * (lpfRealProd S / lpfRealProd D ^ (2 : ℕ))
    else 0

private theorem lpfApprox_eq_main (P R : Finset Nat.Primes)
    (hPR : P ⊆ R) : lpfApprox P R = lpfMain P R := by
  rw [lpfMain_eq_disjointBoolean P R hPR]
  unfold lpfApprox
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro D hD
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro S hS
  split_ifs with hdisj
  · rw [lpfNumeratorWeight_prod, lpfDenominatorWeight_prod]
    unfold lpfCoeff
    ring
  · ring

private theorem lpfFull_approx_error (P R : Finset Nat.Primes) {q : ℕ}
    (hq : 0 < q) (hPR : P ⊆ R) :
    |(q : ℝ) ^ (2 : ℕ) * routeELargestPrimeFullFibre P R q - lpfMain P R| ≤
      6 * lpfB P / (q : ℝ) := by
  have heq : (q : ℝ) ^ (2 : ℕ) * routeELargestPrimeFullFibre P R q -
        lpfApprox P R =
      ∑ D ∈ R.powerset, ∑ S ∈ P.powerset,
        if Disjoint S D then
          lpfCoeff S D *
            ((q : ℝ) ^ (2 : ℕ) * routeEPrimitiveConeWeight
                (lpfRealProd S) ((q : ℝ) * lpfRealProd D) -
              lpfRealProd S / lpfRealProd D ^ (2 : ℕ))
        else 0 := by
    unfold routeELargestPrimeFullFibre lpfApprox
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro D hD
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro S hS
    split_ifs <;> ring
  rw [← lpfApprox_eq_main P R hPR, heq]
  exact (lpfAbs_double_sum_le R.powerset P.powerset
      (fun D S => if Disjoint S D then
        lpfCoeff S D *
          ((q : ℝ) ^ (2 : ℕ) * routeEPrimitiveConeWeight
              (lpfRealProd S) ((q : ℝ) * lpfRealProd D) -
            lpfRealProd S / lpfRealProd D ^ (2 : ℕ)) else 0)
      (fun D S => 3 * lpfRealProd S ^ (2 : ℕ) /
        ((q : ℝ) * lpfRealProd D ^ (3 : ℕ)))
      (by
        intro D hD S hS
        split_ifs
        · exact lpfSigned_remainder_bound S D hq
        · simp
          have ha := lpfRealProd_pos S
          have hd := lpfRealProd_pos D
          have hqR : (0 : ℝ) < q := by exact_mod_cast hq
          positivity)).trans (lpfWeighted_error_le P R hq)

private theorem lpfTail_weighted_le (P R : Finset Nat.Primes) {q : ℕ}
    (hq : 2 ≤ q) :
    (∑ D ∈ R.powerset, ∑ S ∈ P.powerset,
      if q ≤ lpfNatProd D then
        lpfRealProd S / lpfRealProd D ^ (2 : ℕ) else 0) ≤
      2 * lpfB P / (q : ℝ) := by
  have hfactor :
      (∑ D ∈ R.powerset, ∑ S ∈ P.powerset,
        if q ≤ lpfNatProd D then
          lpfRealProd S / lpfRealProd D ^ (2 : ℕ) else 0) =
        (∑ S ∈ P.powerset, lpfRealProd S) *
          (∑ D ∈ R.powerset,
            if q ≤ lpfNatProd D then
              1 / lpfRealProd D ^ (2 : ℕ) else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro D hD
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro S hS
    split_ifs <;> ring
  have hA := lpfSumSq_le P
  have hT : (∑ D ∈ R.powerset,
      if q ≤ lpfNatProd D then
        1 / lpfRealProd D ^ (2 : ℕ) else 0) ≤
      1 / ((q : ℝ) - 1) := by
    simpa only [← lpfNatProd_cast] using lpfTail_sq_le R hq
  have hTnon : 0 ≤ (∑ D ∈ R.powerset,
      if q ≤ lpfNatProd D then
        1 / lpfRealProd D ^ (2 : ℕ) else 0) := by
    apply Finset.sum_nonneg
    intro D hD
    split_ifs <;> positivity
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hInv : 1 / ((q : ℝ) - 1) ≤ 2 / (q : ℝ) := by
    apply (div_le_div_iff₀ (by linarith : (0 : ℝ) < (q : ℝ) - 1)
      (by linarith : (0 : ℝ) < q)).2
    nlinarith
  rw [hfactor]
  calc
    _ ≤ lpfB P * (∑ D ∈ R.powerset,
          if q ≤ lpfNatProd D then
            1 / lpfRealProd D ^ (2 : ℕ) else 0) :=
      mul_le_mul_of_nonneg_right hA hTnon
    _ ≤ lpfB P * (1 / ((q : ℝ) - 1)) :=
      mul_le_mul_of_nonneg_left hT (lpfB_pos P).le
    _ ≤ lpfB P * (2 / (q : ℝ)) :=
      mul_le_mul_of_nonneg_left hInv (lpfB_pos P).le
    _ = 2 * lpfB P / (q : ℝ) := by ring

private theorem lpfCut_error (P R : Finset Nat.Primes) {q : ℕ}
    (hq : 2 ≤ q) (hPR : P ⊆ R) :
    |(q : ℝ) ^ (2 : ℕ) * routeELargestPrimeCutFibre P R q - lpfMain P R| ≤
      8 * lpfB P / (q : ℝ) := by
  have hqpos : 0 < q := by omega
  have htailEq : (q : ℝ) ^ (2 : ℕ) *
        (routeELargestPrimeFullFibre P R q -
          routeELargestPrimeCutFibre P R q) =
      ∑ D ∈ R.powerset, ∑ S ∈ P.powerset,
        if Disjoint S D ∧ q ≤ lpfNatProd D then
          lpfCoeff S D * (q : ℝ) ^ (2 : ℕ) *
            routeEPrimitiveConeWeight
              (lpfRealProd S) ((q : ℝ) * lpfRealProd D)
        else 0 := by
    unfold routeELargestPrimeFullFibre routeELargestPrimeCutFibre
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro D hD
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro S hS
    by_cases hdisj : Disjoint S D
    · by_cases hlt : lpfNatProd D < q
      · simp [hdisj, hlt, Nat.not_le.mpr hlt]
      · have hle : q ≤ lpfNatProd D := by omega
        simp [hdisj, hlt, hle]
        ring
    · simp [hdisj]
  have htail : |(q : ℝ) ^ (2 : ℕ) *
        (routeELargestPrimeFullFibre P R q -
          routeELargestPrimeCutFibre P R q)| ≤
      2 * lpfB P / (q : ℝ) := by
    rw [htailEq]
    exact (lpfAbs_double_sum_le R.powerset P.powerset
        (fun D S => if Disjoint S D ∧ q ≤ lpfNatProd D then
          lpfCoeff S D * (q : ℝ) ^ (2 : ℕ) *
            routeEPrimitiveConeWeight
              (lpfRealProd S) ((q : ℝ) * lpfRealProd D) else 0)
        (fun D S => if q ≤ lpfNatProd D then
          lpfRealProd S / lpfRealProd D ^ (2 : ℕ) else 0)
        (by
          intro D hD S hS
          split_ifs with hboth hlarge
          · have hrem := routeEPrimitive_scaled_remainder_bound
              (a := lpfRealProd S) (d := lpfRealProd D) (q := (q : ℝ))
              (lpfRealProd_pos S).le (lpfRealProd_pos D)
              (by exact_mod_cast hqpos)
            have hK : 0 ≤ (q : ℝ) ^ (2 : ℕ) *
                routeEPrimitiveConeWeight
                  (lpfRealProd S) ((q : ℝ) * lpfRealProd D) := by
              have ha := lpfRealProd_pos S
              have hd := lpfRealProd_pos D
              have hqR : (0 : ℝ) < q := by exact_mod_cast hqpos
              unfold routeEPrimitiveConeWeight
              positivity
            calc
              |lpfCoeff S D * (q : ℝ) ^ (2 : ℕ) *
                    routeEPrimitiveConeWeight
                      (lpfRealProd S) ((q : ℝ) * lpfRealProd D)| =
                  |lpfCoeff S D * ((q : ℝ) ^ (2 : ℕ) *
                    routeEPrimitiveConeWeight
                      (lpfRealProd S) ((q : ℝ) * lpfRealProd D))| := by
                congr 1
                ring
              _ = (q : ℝ) ^ (2 : ℕ) * routeEPrimitiveConeWeight
                    (lpfRealProd S) ((q : ℝ) * lpfRealProd D) := by
                rw [abs_mul, lpfCoeff_abs, one_mul, abs_of_nonneg hK]
              _ ≤ _ := by linarith [hrem.1]
          · exact False.elim (hlarge hboth.2)
          · simp
            have ha := lpfRealProd_pos S
            have hd := lpfRealProd_pos D
            positivity
          · simp)).trans (lpfTail_weighted_le P R hq)
  have heq : (q : ℝ) ^ (2 : ℕ) * routeELargestPrimeCutFibre P R q -
        lpfMain P R =
      ((q : ℝ) ^ (2 : ℕ) * routeELargestPrimeFullFibre P R q -
        lpfMain P R) -
        (q : ℝ) ^ (2 : ℕ) *
          (routeELargestPrimeFullFibre P R q -
            routeELargestPrimeCutFibre P R q) := by ring
  rw [heq]
  calc
    _ ≤ |(q : ℝ) ^ (2 : ℕ) * routeELargestPrimeFullFibre P R q -
          lpfMain P R| +
        |(q : ℝ) ^ (2 : ℕ) *
          (routeELargestPrimeFullFibre P R q -
            routeELargestPrimeCutFibre P R q)| := abs_sub _ _
    _ ≤ 6 * lpfB P / (q : ℝ) + 2 * lpfB P / (q : ℝ) :=
      add_le_add (lpfFull_approx_error P R hqpos hPR) htail
    _ = _ := by ring

/-- A selected numerator Boolean cube retains its parity after completing all
squarefree denominator cofactors in `R` below `q`, even at much smaller prime
scale than the quadratic-mass threshold. The condition retains the actual
Euler-factor margin rather than replacing it by `1`. -/
theorem routeELargestPrimeCutFibre_parity_margin
    (P R : Finset Nat.Primes) {q : ℕ}
    (hq : 3 ≤ q) (hPR : P ⊆ R)
    (hR : ∀ p ∈ R, (p : ℕ) < q)
    (hscale : 32 * routeELargestPrimeQuadraticMass P <
      (q : ℝ) * routeELargestPrimeParityMargin P) :
    routeELargestPrimeParityMargin P / 4 <
      (-1 : ℝ) ^ (P.card + 1) * (q : ℝ) ^ (2 : ℕ) *
        routeELargestPrimeCutFibre P R q := by
  have hq2 : 2 ≤ q := by omega
  have hqR : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 3) hq)
  have hmain := lpfMain_sign P R hq hR
  have herr := lpfCut_error P R hq2 hPR
  have hsign : |(-1 : ℝ) ^ (P.card + 1)| = 1 := by simp
  have herr' :
      |(-1 : ℝ) ^ (P.card + 1) *
        ((q : ℝ) ^ (2 : ℕ) * routeELargestPrimeCutFibre P R q -
          lpfMain P R)| ≤
      8 * lpfB P / (q : ℝ) := by
    simpa only [abs_mul, hsign, one_mul] using herr
  have hlower := (abs_le.mp herr').1
  have hmargin :
      8 * lpfB P / (q : ℝ) < routeELargestPrimeParityMargin P / 4 := by
    apply (div_lt_iff₀ hqR).2
    change 32 * lpfB P < (q : ℝ) * routeELargestPrimeParityMargin P at hscale
    nlinarith
  have hdecomp :
      (-1 : ℝ) ^ (P.card + 1) * (q : ℝ) ^ (2 : ℕ) *
          routeELargestPrimeCutFibre P R q =
        (-1 : ℝ) ^ (P.card + 1) * lpfMain P R +
        (-1 : ℝ) ^ (P.card + 1) *
          ((q : ℝ) ^ (2 : ℕ) * routeELargestPrimeCutFibre P R q -
            lpfMain P R) := by ring
  rw [hdecomp]
  linarith

theorem routeELargestPrimeCutFibre_parity_sign
    (P R : Finset Nat.Primes) {q : ℕ}
    (hq : 3 ≤ q) (hPR : P ⊆ R)
    (hR : ∀ p ∈ R, (p : ℕ) < q)
    (hscale : 32 * routeELargestPrimeQuadraticMass P <
      (q : ℝ) * routeELargestPrimeParityMargin P) :
    (1 / 4 : ℝ) <
      (-1 : ℝ) ^ (P.card + 1) * (q : ℝ) ^ (2 : ℕ) *
        routeELargestPrimeCutFibre P R q := by
  have hC := lpfC_one_le P
  have hmain := routeELargestPrimeCutFibre_parity_margin P R hq hPR hR hscale
  linarith

/-- In the moving one-prime band, completing all denominator cofactors in `R`
leaves a harmonic-size positive source contribution. -/
theorem routeELargestPrimeOnePrime_harmonic_lower
    (p : Nat.Primes) (R : Finset Nat.Primes) {q : ℕ}
    (hpR : p ∈ R) (hR : ∀ r ∈ R, (r : ℕ) < q)
    (hlow : 256 * (p : ℕ) ≤ q) (hhigh : q ≤ 1024 * (p : ℕ)) :
    1 / (8192 * (q : ℝ)) < routeELargestPrimeCutFibre {p} R q := by
  have hp : (2 : ℝ) ≤ p := by exact_mod_cast p.property.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hpNat : 2 ≤ (p : ℕ) := p.property.two_le
  have hq3 : 3 ≤ q := by omega
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 3) hq3)
  have hqlo : 256 * (p : ℝ) ≤ q := by exact_mod_cast hlow
  have hqhi : (q : ℝ) ≤ 1024 * (p : ℝ) := by exact_mod_cast hhigh
  have hC : (p : ℝ) / 2 ≤ routeELargestPrimeParityMargin {p} := by
    simp only [routeELargestPrimeParityMargin, Finset.prod_singleton]
    have hnonneg : 0 ≤ 1 / (p : ℝ) ^ (2 : ℕ) := by positivity
    linarith
  have hB : routeELargestPrimeQuadraticMass {p} ≤
      2 * (p : ℝ) ^ (2 : ℕ) := by
    simp only [routeELargestPrimeQuadraticMass, Finset.prod_singleton]
    nlinarith [sq_nonneg ((p : ℝ) - 1)]
  have hC0 : 0 ≤ routeELargestPrimeParityMargin {p} := by linarith
  have hscale₁ := mul_le_mul_of_nonneg_right hqlo hC0
  have hscale₂ := mul_le_mul_of_nonneg_left hC
    (by positivity : 0 ≤ 256 * (p : ℝ))
  have hscale : 32 * routeELargestPrimeQuadraticMass {p} <
      (q : ℝ) * routeELargestPrimeParityMargin {p} := by
    nlinarith [sq_pos_of_pos hp0]
  have hmargin := routeELargestPrimeCutFibre_parity_margin
    {p} R hq3 (Finset.singleton_subset_iff.mpr hpR) hR hscale
  have hmargin' : routeELargestPrimeParityMargin {p} / 4 <
      (q : ℝ) ^ (2 : ℕ) * routeELargestPrimeCutFibre {p} R q := by
    simpa using hmargin
  have hfloor : (q : ℝ) / 8192 ≤ routeELargestPrimeParityMargin {p} / 4 := by
    linarith
  have htarget : (q : ℝ) / 8192 <
      (q : ℝ) ^ (2 : ℕ) * routeELargestPrimeCutFibre {p} R q :=
    lt_of_le_of_lt hfloor hmargin'
  have hfrac : ((q : ℝ) / 8192) / (q : ℝ) ^ (2 : ℕ) =
      1 / (8192 * (q : ℝ)) := by
    field_simp
  rw [← hfrac]
  exact (div_lt_iff₀ (sq_pos_of_pos hq0)).2 (by nlinarith [htarget])

/-- Exactly the available prime factors of a denominator cofactor below `q`. -/
noncomputable def routeELargestPrimeCofactorSet (q : ℕ) : Finset Nat.Primes := by
  classical
  exact (Nat.primesBelow q).attach.image
    (fun n => (⟨n.1, Nat.prime_of_mem_primesBelow n.2⟩ : Nat.Primes))

theorem mem_routeELargestPrimeCofactorSet (p : Nat.Primes) (q : ℕ) :
    p ∈ routeELargestPrimeCofactorSet q ↔ (p : ℕ) < q := by
  classical
  unfold routeELargestPrimeCofactorSet
  constructor
  · intro hp
    obtain ⟨n, hn, hnp⟩ := Finset.mem_image.mp hp
    have hval : (n : ℕ) = (p : ℕ) := congrArg Subtype.val hnp
    rw [← hval]
    exact Nat.lt_of_mem_primesBelow n.property
  · intro hp
    have hmem : (p : ℕ) ∈ Nat.primesBelow q :=
      Nat.mem_primesBelow.mpr ⟨hp, p.property⟩
    apply Finset.mem_image.mpr
    refine ⟨⟨(p : ℕ), hmem⟩, Finset.mem_attach _ _, ?_⟩
    exact Subtype.ext rfl

private theorem lpfBandPrime_exists {q : ℕ} (hq : 1024 ≤ q) :
    ∃ p : Nat.Primes,
      256 * (p : ℕ) ≤ q ∧ q ≤ 1024 * (p : ℕ) := by
  let n := q / 512
  have hn : n ≠ 0 := by dsimp [n]; omega
  obtain ⟨p, hp, hnp, hpn⟩ := Nat.exists_prime_lt_and_le_two_mul n hn
  refine ⟨⟨p, hp⟩, ?_, ?_⟩
  · dsimp [n] at hnp hpn ⊢
    omega
  · dsimp [n] at hnp hpn ⊢
    omega

private noncomputable def lpfBandPrime (q : Nat.Primes) : Nat.Primes :=
  if h : 1024 ≤ (q : ℕ) then Classical.choose (lpfBandPrime_exists h)
  else ⟨2, by norm_num⟩

private theorem lpfBandPrime_bounds (q : Nat.Primes)
    (hq : 1024 ≤ (q : ℕ)) :
    256 * (lpfBandPrime q : ℕ) ≤ (q : ℕ) ∧
      (q : ℕ) ≤ 1024 * (lpfBandPrime q : ℕ) := by
  simpa only [lpfBandPrime, dif_pos hq] using
    Classical.choose_spec (lpfBandPrime_exists hq)

/-- One moving numerator prime is chosen by Bertrand in a fixed proportional
window. The denominator cofactor sum remains complete below each `q`. -/
noncomputable def routeELargestPrimeHarmonicSelected (q : Nat.Primes) : ℝ :=
  if 1024 ≤ (q : ℕ) then
    routeELargestPrimeCutFibre {lpfBandPrime q}
      (routeELargestPrimeCofactorSet q) q
  else 0

theorem routeELargestPrimeHarmonicSelected_lower (q : Nat.Primes) :
    (if 1024 ≤ (q : ℕ) then 1 / (8192 * (q : ℝ)) else 0) ≤
      routeELargestPrimeHarmonicSelected q := by
  by_cases hq : 1024 ≤ (q : ℕ)
  · simp only [hq, ↓reduceIte, routeELargestPrimeHarmonicSelected]
    have hband := lpfBandPrime_bounds q hq
    have hpq : (lpfBandPrime q : ℕ) < (q : ℕ) := by
      have hp2 := (lpfBandPrime q).property.two_le
      omega
    exact (routeELargestPrimeOnePrime_harmonic_lower
      (lpfBandPrime q) (routeELargestPrimeCofactorSet q)
      ((mem_routeELargestPrimeCofactorSet _ _).2 hpq)
      (fun r hr => (mem_routeELargestPrimeCofactorSet r q).1 hr)
      hband.1 hband.2).le
  · simp [routeELargestPrimeHarmonicSelected, hq]

/-- A sign-locked, physical-cutoff selected subfamily is not absolutely
summable across prime largest-denominator fibres. Any cancellation in the
complete covariance must come from other numerator channels. -/
private theorem lpf_not_summable_harmonic_tail (N : ℕ) :
    ¬ Summable (fun q : Nat.Primes =>
      if N ≤ (q : ℕ) then 1 / (8192 * (q : ℝ)) else 0) := by
  intro hsum
  have hfinite : {q : Nat.Primes | (q : ℕ) < N}.Finite := by
    convert (routeELargestPrimeCofactorSet N).finite_toSet using 1
    ext q
    simp only [Finset.mem_coe, Set.mem_setOf_eq,
      mem_routeELargestPrimeCofactorSet]
  have hevent :
      (fun q : Nat.Primes =>
        if N ≤ (q : ℕ) then 1 / (8192 * (q : ℝ)) else 0) =ᶠ[Filter.cofinite]
      (fun q : Nat.Primes => 1 / (8192 * (q : ℝ))) := by
    rw [Filter.EventuallyEq, Filter.eventually_cofinite]
    refine hfinite.subset ?_
    intro q hq
    simp only [Set.mem_setOf_eq] at hq ⊢
    by_contra hnot
    have hge : N ≤ (q : ℕ) := by omega
    simp [hge] at hq
  have hscaled := hsum.congr_cofinite hevent
  have hscaled' : Summable (fun q : Nat.Primes =>
      (1 / 8192 : ℝ) * (1 / (q : ℝ))) := by
    have hfun : (fun q : Nat.Primes =>
        (1 / 8192 : ℝ) * (1 / (q : ℝ))) =
        (fun q : Nat.Primes => 1 / (8192 * (q : ℝ))) := by
      funext q
      have hq : (q : ℝ) ≠ 0 := by exact_mod_cast q.property.ne_zero
      field_simp
    rw [hfun]
    exact hscaled
  have hharmonic : Summable (fun q : Nat.Primes => 1 / (q : ℝ)) :=
    (summable_mul_left_iff (by norm_num : (1 / 8192 : ℝ) ≠ 0)).mp hscaled'
  exact Nat.Primes.not_summable_one_div hharmonic

theorem not_summable_routeELargestPrimeHarmonicSelected :
    ¬ Summable routeELargestPrimeHarmonicSelected := by
  intro hsum
  have hminor : Summable (fun q : Nat.Primes =>
      if 1024 ≤ (q : ℕ) then 1 / (8192 * (q : ℝ)) else 0) :=
    Summable.of_nonneg_of_le
      (fun q => by split_ifs <;> positivity)
      routeELargestPrimeHarmonicSelected_lower hsum
  exact lpf_not_summable_harmonic_tail 1024 hminor

/-- The same unconditional divergence, now stated with the literal arithmetic
Möbius coefficients of both source endpoints. -/
theorem not_summable_routeELargestPrimeMobiusSelected :
    ¬ Summable (fun q : Nat.Primes =>
      if 1024 ≤ (q : ℕ) then
        routeELargestPrimeMobiusFibre {lpfBandPrime q}
          (routeELargestPrimeCofactorSet q) q
      else 0) := by
  have heq : (fun q : Nat.Primes =>
      if 1024 ≤ (q : ℕ) then
        routeELargestPrimeMobiusFibre {lpfBandPrime q}
          (routeELargestPrimeCofactorSet q) q
      else 0) = routeELargestPrimeHarmonicSelected := by
    funext q
    by_cases hq : 1024 ≤ (q : ℕ)
    · simp only [hq, ↓reduceIte, routeELargestPrimeHarmonicSelected]
      exact routeELargestPrimeMobiusFibre_eq_cut _ _ q
        (fun r hr => (mem_routeELargestPrimeCofactorSet r q).1 hr)
    · simp [routeELargestPrimeHarmonicSelected, hq]
  rw [heq]
  exact not_summable_routeELargestPrimeHarmonicSelected

/-- A coefficient-one numerator-prime channel, not a Boolean cube. The source
is the literal pair `μ(p) μ(qd) K(p,qd)` for every admitted cofactor `d`. -/
noncomputable def routeELargestPrimePrimeNumeratorFibre
    (p q : Nat.Primes) (R : Finset Nat.Primes) : ℝ :=
  ∑ D ∈ R.powerset,
    if p ∉ D ∧ lpfNatProd D < (q : ℕ) then
      (ArithmeticFunction.moebius (p : ℕ) : ℝ) *
        (ArithmeticFunction.moebius ((q : ℕ) * lpfNatProd D) : ℝ) *
          routeEPrimitiveConeWeight
            (p : ℝ) ((q : ℝ) * lpfRealProd D)
    else 0

private theorem lpfPowerset_singleton (p : Nat.Primes) :
    ({p} : Finset Nat.Primes).powerset = {∅, {p}} := by
  classical
  ext S
  simp only [Finset.mem_powerset, Finset.mem_insert, Finset.mem_singleton,
    Finset.subset_singleton_iff]

private theorem lpfPowerset_pair (a b : Nat.Primes) (_hab : a ≠ b) :
    ({a, b} : Finset Nat.Primes).powerset = {∅, {a}, {b}, {a, b}} := by
  classical
  rw [Finset.powerset_insert]
  rw [lpfPowerset_singleton]
  simp only [Finset.image_insert, Finset.image_singleton, Finset.insert_empty]
  ext S
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  tauto

private theorem lpfSumPowerset_pair (a b : Nat.Primes) (hab : a ≠ b)
    (f : Finset Nat.Primes → ℝ) :
    ∑ S ∈ ({a, b} : Finset Nat.Primes).powerset, f S =
      f ∅ + f {a} + f {b} + f {a, b} := by
  rw [lpfPowerset_pair a b hab]
  have h0 : (∅ : Finset Nat.Primes) ∉
      ({{a}, {b}, {a, b}} : Finset (Finset Nat.Primes)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨by simp, by simp, ?_⟩
    intro heq
    have ha : a ∈ (∅ : Finset Nat.Primes) := heq ▸ (by simp)
    simp at ha
  have h1 : ({a} : Finset Nat.Primes) ∉
      ({{b}, {a, b}} : Finset (Finset Nat.Primes)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    constructor
    · simpa using hab
    · intro heq
      have hb : b ∈ ({a} : Finset Nat.Primes) := heq ▸ (by simp)
      simp only [Finset.mem_singleton] at hb
      exact hab hb.symm
  have h2 : ({b} : Finset Nat.Primes) ∉
      ({{a, b}} : Finset (Finset Nat.Primes)) := by
    simp only [Finset.mem_singleton]
    intro heq
    have ha : a ∈ ({b} : Finset Nat.Primes) := heq ▸ (by simp)
    simp only [Finset.mem_singleton] at ha
    exact hab ha
  simp only [Finset.sum_insert h0, Finset.sum_insert h1,
    Finset.sum_insert h2, Finset.sum_singleton]
  ac_rfl

private theorem lpfSumPowerset_singleton (a : Nat.Primes)
    (f : Finset Nat.Primes → ℝ) :
    ∑ S ∈ ({a} : Finset Nat.Primes).powerset, f S = f ∅ + f {a} := by
  rw [lpfPowerset_singleton]
  simp only [Finset.sum_insert (by simp :
    (∅ : Finset Nat.Primes) ∉ ({{a}} : Finset (Finset Nat.Primes))),
    Finset.sum_singleton]

private theorem lpfPairIncrement (a b : Nat.Primes) (hab : a ≠ b)
    (f : Finset Nat.Primes → ℝ) :
    (∑ S ∈ ({a, b} : Finset Nat.Primes).powerset, f S) -
      (∑ S ∈ ({a} : Finset Nat.Primes).powerset, f S) =
        f {b} + f {a, b} := by
  rw [lpfSumPowerset_pair a b hab, lpfSumPowerset_singleton]
  ring

/-- The singleton Boolean cube is exactly the disjoint union of the empty
numerator channel and the prime numerator channel; no overlapping cubes are
summed in the latter. -/
theorem routeELargestPrimeSingleton_eq_empty_add_prime
    (p q : Nat.Primes) (R : Finset Nat.Primes) :
    routeELargestPrimeMobiusFibre {p} R q =
      routeELargestPrimeMobiusFibre ∅ R q +
        routeELargestPrimePrimeNumeratorFibre p q R := by
  classical
  unfold routeELargestPrimeMobiusFibre
    routeELargestPrimePrimeNumeratorFibre
  rw [lpfPowerset_singleton, Finset.powerset_empty]
  simp only [Finset.sum_insert (by simp : (∅ : Finset Nat.Primes) ∉
    ({{p}} : Finset (Finset Nat.Primes))), Finset.sum_singleton]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro D hD
  by_cases hpD : p ∈ D
  · simp [hpD, Finset.disjoint_left]
  · simp [hpD, Finset.disjoint_left, lpfNatProd, lpfRealProd]

private theorem lpfEmptyNumerator_nonpos (q : Nat.Primes)
    (hq : 1024 ≤ (q : ℕ)) :
    routeELargestPrimeMobiusFibre ∅ (routeELargestPrimeCofactorSet q) q ≤ 0 := by
  have hq3 : 3 ≤ (q : ℕ) := by omega
  have hq32 : (32 : ℝ) < q := by exact_mod_cast (show 32 < (q : ℕ) by omega)
  have hscale : 32 * routeELargestPrimeQuadraticMass ∅ <
      (q : ℝ) * routeELargestPrimeParityMargin ∅ := by
    simpa [routeELargestPrimeQuadraticMass,
      routeELargestPrimeParityMargin] using hq32
  have hsign := routeELargestPrimeCutFibre_parity_sign
    ∅ (routeELargestPrimeCofactorSet q) hq3 (by simp)
      (fun r hr => (mem_routeELargestPrimeCofactorSet r q).1 hr) hscale
  have hqpos : (0 : ℝ) < q := by exact_mod_cast q.property.pos
  have hq2 : 0 < (q : ℝ) ^ (2 : ℕ) := sq_pos_of_pos hqpos
  rw [routeELargestPrimeMobiusFibre_eq_cut
    ∅ (routeELargestPrimeCofactorSet q) q
      (fun r hr => (mem_routeELargestPrimeCofactorSet r q).1 hr)]
  norm_num at hsign
  nlinarith

/-- The harmonic lower bound belongs to a disjoint prime-numerator channel,
not merely to an overlapping Boolean cube. -/
theorem routeELargestPrimePrimeNumerator_harmonic_lower
    (p q : Nat.Primes) (hlow : 256 * (p : ℕ) ≤ (q : ℕ))
    (hhigh : (q : ℕ) ≤ 1024 * (p : ℕ))
    (hq : 1024 ≤ (q : ℕ)) :
    1 / (8192 * (q : ℝ)) <
      routeELargestPrimePrimeNumeratorFibre p q
        (routeELargestPrimeCofactorSet q) := by
  let R := routeELargestPrimeCofactorSet q
  have hpq : (p : ℕ) < (q : ℕ) := by
    have hp2 := p.property.two_le
    omega
  have hR : ∀ r ∈ R, (r : ℕ) < (q : ℕ) :=
    fun r hr => (mem_routeELargestPrimeCofactorSet r q).1 hr
  have hcut := routeELargestPrimeOnePrime_harmonic_lower p R
    ((mem_routeELargestPrimeCofactorSet p q).2 hpq) hR hlow hhigh
  have hmob : 1 / (8192 * (q : ℝ)) <
      routeELargestPrimeMobiusFibre {p} R q := by
    rwa [routeELargestPrimeMobiusFibre_eq_cut {p} R q hR]
  have hempty := lpfEmptyNumerator_nonpos q hq
  have hpart := routeELargestPrimeSingleton_eq_empty_add_prime p q R
  dsimp [R] at hpart hmob ⊢
  linarith

/-- The canonical Bertrand-selected coefficient-one source prime channel. -/
noncomputable def routeELargestPrimePrimeNumeratorSelected (q : Nat.Primes) : ℝ :=
  if 1024 ≤ (q : ℕ) then
    routeELargestPrimePrimeNumeratorFibre (lpfBandPrime q) q
      (routeELargestPrimeCofactorSet q)
  else 0

theorem routeELargestPrimeHarmonicSelected_le_primeNumeratorSelected
    (q : Nat.Primes) :
    routeELargestPrimeHarmonicSelected q ≤
      routeELargestPrimePrimeNumeratorSelected q := by
  by_cases hq : 1024 ≤ (q : ℕ)
  · simp only [hq, ↓reduceIte, routeELargestPrimeHarmonicSelected,
      routeELargestPrimePrimeNumeratorSelected]
    have hR : ∀ r ∈ routeELargestPrimeCofactorSet q,
        (r : ℕ) < (q : ℕ) :=
      fun r hr => (mem_routeELargestPrimeCofactorSet r q).1 hr
    have hpart := routeELargestPrimeSingleton_eq_empty_add_prime
      (lpfBandPrime q) q (routeELargestPrimeCofactorSet q)
    have hmob := routeELargestPrimeMobiusFibre_eq_cut
      {lpfBandPrime q} (routeELargestPrimeCofactorSet q) q hR
    have hempty := lpfEmptyNumerator_nonpos q hq
    linarith
  · simp [routeELargestPrimeHarmonicSelected,
      routeELargestPrimePrimeNumeratorSelected, hq]

/-- Harmonic divergence survives after deleting the shared empty-numerator
term: every selected pair has exactly one prime numerator and distinct largest
denominator prime. -/
theorem not_summable_routeELargestPrimePrimeNumeratorSelected :
    ¬ Summable routeELargestPrimePrimeNumeratorSelected := by
  intro hsum
  have hminor : Summable routeELargestPrimeHarmonicSelected :=
    Summable.of_nonneg_of_le
      (fun q => (routeELargestPrimeHarmonicSelected_lower q).trans'
        (by split_ifs <;> positivity))
      routeELargestPrimeHarmonicSelected_le_primeNumeratorSelected hsum
  exact not_summable_routeELargestPrimeHarmonicSelected hminor

/-- The coefficient-one increment obtained by activating a second numerator
prime `2` above the `2`-only source. Its new numerator supports are `p` and
`2p`; the old empty and `2` supports cancel in the difference. -/
noncomputable def routeELargestPrimeTwoActivatedIncrement
    (p q : Nat.Primes) : ℝ :=
  let two : Nat.Primes := ⟨2, by norm_num⟩
  routeELargestPrimeMobiusFibre {two, p}
      (routeELargestPrimeCofactorSet q) q -
    routeELargestPrimeMobiusFibre {two}
      (routeELargestPrimeCofactorSet q) q

/-- The second new numerator support in the `2`-activated increment is the
literal composite `2p` source, after all allowed denominator cofactors. -/
noncomputable def routeELargestPrimeTwoPrimeNumeratorFibre
    (p q : Nat.Primes) (R : Finset Nat.Primes) : ℝ :=
  let two : Nat.Primes := ⟨2, by norm_num⟩
  ∑ D ∈ R.powerset,
    if Disjoint ({two, p} : Finset Nat.Primes) D ∧
        lpfNatProd D < (q : ℕ) then
      (ArithmeticFunction.moebius ((2 : ℕ) * (p : ℕ)) : ℝ) *
        (ArithmeticFunction.moebius ((q : ℕ) * lpfNatProd D) : ℝ) *
          routeEPrimitiveConeWeight
            ((2 : ℝ) * (p : ℝ)) ((q : ℝ) * lpfRealProd D)
    else 0

/-- Exact disjoint-source decomposition: adding numerator prime `p` above
`{2}` creates only the prime `p` and composite `2p` channels. -/
theorem routeELargestPrimeTwoActivatedIncrement_eq_prime_add_composite
    (p q : Nat.Primes) (hp3 : 3 ≤ (p : ℕ)) :
    routeELargestPrimeTwoActivatedIncrement p q =
      routeELargestPrimePrimeNumeratorFibre p q
        (routeELargestPrimeCofactorSet q) +
      routeELargestPrimeTwoPrimeNumeratorFibre p q
        (routeELargestPrimeCofactorSet q) := by
  classical
  let two : Nat.Primes := ⟨2, by norm_num⟩
  have hne : two ≠ p := by
    intro h
    have hp : (p : ℕ) = 2 := congrArg Subtype.val h.symm
    omega
  change routeELargestPrimeMobiusFibre {two, p}
      (routeELargestPrimeCofactorSet q) q -
      routeELargestPrimeMobiusFibre {two}
        (routeELargestPrimeCofactorSet q) q =
      routeELargestPrimePrimeNumeratorFibre p q
        (routeELargestPrimeCofactorSet q) +
      routeELargestPrimeTwoPrimeNumeratorFibre p q
        (routeELargestPrimeCofactorSet q)
  unfold routeELargestPrimeMobiusFibre
    routeELargestPrimePrimeNumeratorFibre
    routeELargestPrimeTwoPrimeNumeratorFibre
  dsimp only
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro D hD
  rw [lpfPairIncrement two p hne]
  by_cases htwoD : two ∈ D
  · have htwoAny : ∀ r : Nat.Primes, (r : ℕ) = 2 → r ∈ D := by
      intro r hr
      have hre : r = two := Subtype.ext (by simpa [two] using hr)
      exact hre ▸ htwoD
    simp [htwoD, Finset.disjoint_left, lpfNatProd, lpfRealProd]
    intro hnot
    exact (hnot (htwoAny _ rfl)).elim
  by_cases hpD : p ∈ D
  · simp [hpD, Finset.disjoint_left]
  simp [htwoD, hpD, Finset.disjoint_left, lpfNatProd,
    lpfRealProd, two, hne]

/-- The first composite numerator channel overpays the harmonic prime-only
channel after every smaller-prime denominator cofactor is completed. -/
theorem routeELargestPrimeTwoActivatedIncrement_negative
    (p q : Nat.Primes) (hp3 : 3 ≤ (p : ℕ))
    (hlow : 256 * (p : ℕ) ≤ (q : ℕ)) :
    routeELargestPrimeTwoActivatedIncrement p q < 0 := by
  let two : Nat.Primes := ⟨2, by norm_num⟩
  let P : Finset Nat.Primes := {two, p}
  let R := routeELargestPrimeCofactorSet q
  have hne : two ≠ p := by
    intro h
    have hp : (p : ℕ) = 2 := congrArg Subtype.val h.symm
    omega
  have hPtwo : P.card = 2 := by simp [P, hne]
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have hp0 : (0 : ℝ) < p := by linarith
  have hqlo : 256 * (p : ℝ) ≤ q := by exact_mod_cast hlow
  have hq3 : 3 ≤ (q : ℕ) := by omega
  have hqR : (0 : ℝ) < q := by exact_mod_cast q.property.pos
  have hR : ∀ r ∈ R, (r : ℕ) < (q : ℕ) :=
    fun r hr => (mem_routeELargestPrimeCofactorSet r q).1 hr
  have hpq : (p : ℕ) < (q : ℕ) := by omega
  have htwoq : (two : ℕ) < (q : ℕ) := by dsimp [two]; omega
  have hPR : P ⊆ R := by
    intro r hr
    simp only [P, Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact (mem_routeELargestPrimeCofactorSet _ _).2 htwoq
    · exact (mem_routeELargestPrimeCofactorSet _ _).2 hpq
  have htwoNot : two ∉ ({p} : Finset Nat.Primes) := by simpa using hne
  have hPmass : routeELargestPrimeQuadraticMass P =
      5 * (1 + (p : ℝ) ^ (2 : ℕ)) := by
    simp only [P, routeELargestPrimeQuadraticMass]
    rw [Finset.prod_insert htwoNot, Finset.prod_singleton]
    norm_num [two]
  have hPmargin : routeELargestPrimeParityMargin P =
      (5 / 4 : ℝ) * ((p : ℝ) + 1 / (p : ℝ) ^ (2 : ℕ) - 1) := by
    simp only [P, routeELargestPrimeParityMargin]
    rw [Finset.prod_insert htwoNot, Finset.prod_singleton]
    norm_num [two]
  have hmassBound : routeELargestPrimeQuadraticMass P ≤
      (50 / 9 : ℝ) * (p : ℝ) ^ (2 : ℕ) := by
    rw [hPmass]
    nlinarith [sq_nonneg ((p : ℝ) - 3)]
  have hmarginBound : (5 / 6 : ℝ) * (p : ℝ) ≤
      routeELargestPrimeParityMargin P := by
    rw [hPmargin]
    have hinv : 0 ≤ 1 / (p : ℝ) ^ (2 : ℕ) := by positivity
    linarith
  have hmargin0 : 0 ≤ routeELargestPrimeParityMargin P := by
    linarith
  have hqmul := mul_le_mul_of_nonneg_right hqlo hmargin0
  have hCmul := mul_le_mul_of_nonneg_left hmarginBound
    (by positivity : 0 ≤ 256 * (p : ℝ))
  have hPscale : 32 * routeELargestPrimeQuadraticMass P <
      (q : ℝ) * routeELargestPrimeParityMargin P := by
    nlinarith [sq_pos_of_pos hp0]
  have hPsign := routeELargestPrimeCutFibre_parity_sign
    P R hq3 hPR hR hPscale
  rw [hPtwo] at hPsign
  norm_num at hPsign
  have hPneg : routeELargestPrimeMobiusFibre P R q < 0 := by
    rw [routeELargestPrimeMobiusFibre_eq_cut P R q hR]
    nlinarith [sq_pos_of_pos hqR]
  have htwoScale : 32 * routeELargestPrimeQuadraticMass {two} <
      (q : ℝ) * routeELargestPrimeParityMargin {two} := by
    simp [routeELargestPrimeQuadraticMass,
      routeELargestPrimeParityMargin, two]
    nlinarith
  have htwoSign := routeELargestPrimeCutFibre_parity_sign
    {two} R hq3 (by
      simp only [Finset.singleton_subset_iff]
      exact (mem_routeELargestPrimeCofactorSet _ _).2 htwoq)
      hR htwoScale
  have htwoPos : 0 < routeELargestPrimeMobiusFibre {two} R q := by
    rw [routeELargestPrimeMobiusFibre_eq_cut {two} R q hR]
    norm_num at htwoSign
    nlinarith [sq_pos_of_pos hqR]
  dsimp [routeELargestPrimeTwoActivatedIncrement, P, R, two] at *
  linarith

/-- The literal composite `2p` source pays more than the disjoint prime `p`
source's harmonic mass in the moving-prime band. This identifies an actual
opposing source channel, rather than inferring payment from cube overlap. -/
theorem routeELargestPrimeTwoPrimeNumerator_harmonic_upper
    (p q : Nat.Primes) (hp3 : 3 ≤ (p : ℕ))
    (hlow : 256 * (p : ℕ) ≤ (q : ℕ))
    (hhigh : (q : ℕ) ≤ 1024 * (p : ℕ))
    (hq : 1024 ≤ (q : ℕ)) :
    routeELargestPrimeTwoPrimeNumeratorFibre p q
      (routeELargestPrimeCofactorSet q) <
        -(1 / (8192 * (q : ℝ))) := by
  have hprime := routeELargestPrimePrimeNumerator_harmonic_lower
    p q hlow hhigh hq
  have hinc := routeELargestPrimeTwoActivatedIncrement_negative
    p q hp3 hlow
  have hsplit := routeELargestPrimeTwoActivatedIncrement_eq_prime_add_composite
    p q hp3
  linarith

/-- The Bertrand-selected literal composite channel opposite the prime
channel, with a finite initial segment removed. -/
noncomputable def routeELargestPrimeCompositeNumeratorSelected
    (q : Nat.Primes) : ℝ :=
  if 4096 ≤ (q : ℕ) then
    routeELargestPrimeTwoPrimeNumeratorFibre (lpfBandPrime q) q
      (routeELargestPrimeCofactorSet q)
  else 0

/-- The disjoint composite-numerator payment has divergent negative mass.
Thus both signs have infinite selected variation before any all-grade
conditional completion. -/
theorem not_summable_routeELargestPrimeCompositeNumeratorSelected :
    ¬ Summable routeELargestPrimeCompositeNumeratorSelected := by
  intro hsum
  have hminor : Summable (fun q : Nat.Primes =>
      if 4096 ≤ (q : ℕ) then 1 / (8192 * (q : ℝ)) else 0) := by
    refine Summable.of_nonneg_of_le
      (fun q => by split_ifs <;> positivity) (fun q => ?_) hsum.neg
    ·
      by_cases hq : 4096 ≤ (q : ℕ)
      · have hband := lpfBandPrime_bounds q (by omega : 1024 ≤ (q : ℕ))
        have hp3 : 3 ≤ (lpfBandPrime q : ℕ) := by
          by_contra hnot
          have hp2 := (lpfBandPrime q).property.two_le
          omega
        have hcomp := routeELargestPrimeTwoPrimeNumerator_harmonic_upper
          (lpfBandPrime q) q hp3 hband.1 hband.2 (by omega)
        simp only [hq, ↓reduceIte, routeELargestPrimeCompositeNumeratorSelected]
        linarith
      · simp [routeELargestPrimeCompositeNumeratorSelected, hq]
  exact lpf_not_summable_harmonic_tail 4096 hminor

end RHTower
