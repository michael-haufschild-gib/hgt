import GaloisForLFunctions.RHTower.Sieve.AffinePairSieve

/-!
# Actual prime dilation-pair sieve

A least solution anchors the complete primitive solution progression. Its affine
discriminant is the literal signed shift, making the finite sieve denominator
independent of the anchor. Exact gcd reduction preserves both cutoffs and excludes
incompatible shifts. Every pair, the anchor and the entire sieve remainder remain.
-/

noncomputable section
open Finset
namespace RHTower.Sieve

/-- Every solution after a least anchor lies on the actual primitive affine progression. -/
theorem exists_primeDilation_parameter {A B p q p₀ q₀ : ℕ} (hB : 0 < B)
    (hcop : A.Coprime B) (hp : p₀ ≤ p) (heq : A * p + B * q₀ = A * p₀ + B * q) :
    ∃ n : ℕ, p = p₀ + B * n ∧ q = q₀ + A * n := by
  have hq : q₀ ≤ q := by
    by_contra hn
    have h1 := Nat.mul_le_mul_left A hp
    have h2 := Nat.mul_lt_mul_of_pos_left (by omega : q < q₀) hB
    omega
  have hprod : A * (p - p₀) = B * (q - q₀) := by
    simp only [Nat.mul_sub_left_distrib]
    omega
  have hd : B ∣ p - p₀ := hcop.symm.dvd_of_dvd_mul_left (hprod ▸ dvd_mul_right B (q - q₀))
  obtain ⟨n, hn⟩ := hd
  have hqn : q - q₀ = A * n := by
    apply Nat.eq_of_mul_eq_mul_left hB
    rw [← hprod, hn]
    ring
  exact ⟨n, by omega, by omega⟩

/-- Every prime/cofactor pair at the literal signed dilation shift. -/
def primeDilationPairs (P Q A B h : ℕ) (v : ℤ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 P).product (Finset.Icc 1 Q)).filter (fun x =>
    x.1.Prime ∧ x.2.Prime ∧ h < x.1 ∧ h < x.2 ∧ (A : ℤ) * x.1 - (B : ℤ) * x.2 = v)

/-- Explicit anchor-independent denominator for the actual dilation shift. -/
def primeDilationBoundingSum (P₁ h A B : ℕ) (v : ℤ) (z : ℝ) : ℝ :=
  ∑ e ∈ (affinePairPrimorial P₁ h B A).divisors, if (e : ℝ) ^ 2 ≤ z then
    ∏ p ∈ e.primeFactors, pairClassCount v.natAbs p / ((p : ℝ) - pairClassCount v.natAbs p) else 0

private theorem primeDilationBoundingSum_nonneg {P₁ : ℕ} (hP₁ : 2 ≤ P₁)
    (h A B : ℕ) (v : ℤ) (z : ℝ) : 0 ≤ primeDilationBoundingSum P₁ h A B v z := by
  apply Finset.sum_nonneg
  intro e he
  split_ifs
  · apply Finset.prod_nonneg
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hdiv : p ∣ affinePairPrimorial P₁ h B A :=
      (Nat.dvd_of_mem_primeFactors hp).trans (Nat.mem_divisors.mp he).1
    have hmem := mem_of_prime_dvd_prod
      (fun _ hp => rangePrimes_prime (Finset.mem_filter.mp hp).1) hprime hdiv
    have hr := (Finset.mem_filter.mp hmem).1
    rw [rangePrimes, Finset.mem_filter, Finset.mem_Icc] at hr
    have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (by omega : 3 ≤ p)
    unfold pairClassCount
    split_ifs <;> apply div_nonneg <;> linarith only [hp3]
  · exact le_rfl

private theorem primeDilationBoundingSum_eq {A B p₀ q₀ : ℕ} {v : ℤ}
    (hv : (A : ℤ) * p₀ - (B : ℤ) * q₀ = v) (P₁ h : ℕ) (z : ℝ) :
    affinePairBoundingSum P₁ h B A p₀ q₀ z = primeDilationBoundingSum P₁ h A B v z := by
  have hdisc : affinePairDiscriminant B A p₀ q₀ = -v := by
    unfold affinePairDiscriminant
    linarith only [hv]
  simp only [affinePairBoundingSum, primeDilationBoundingSum, hdisc, Int.natAbs_neg]

/-- A least prime anchor parametrizes the entire finite dilation-pair set.
This exact count transport is independent of the sieve subsequently applied. -/
theorem exists_primeDilationPairs_anchor_bound (P Q A B h : ℕ) (hB : 0 < B)
    (hcop : A.Coprime B) (v : ℤ) (hne : (primeDilationPairs P Q A B h v).Nonempty) :
    ∃ x₀ ∈ primeDilationPairs P Q A B h v,
      ((primeDilationPairs P Q A B h v).card : ℝ) ≤
        1 + (((Finset.Icc 1 (P / B)).filter (fun n =>
          (B * n + x₀.1).Prime ∧ (A * n + x₀.2).Prime ∧
            h < B * n + x₀.1 ∧ h < A * n + x₀.2)).card : ℝ) := by
  classical
  let S := primeDilationPairs P Q A B h v
  obtain ⟨x₀, hx₀, hmin⟩ := Finset.exists_min_image S Prod.fst hne
  have hdata (x : ℕ × ℕ) (hx : x ∈ S) :
      (1 ≤ x.1 ∧ x.1 ≤ P) ∧ (1 ≤ x.2 ∧ x.2 ≤ Q) ∧
      x.1.Prime ∧ x.2.Prime ∧ h < x.1 ∧ h < x.2 ∧
      (A : ℤ) * x.1 - (B : ℤ) * x.2 = v := by
    have hh := Finset.mem_filter.mp hx
    have hw := Finset.mem_product.mp hh.1
    exact ⟨Finset.mem_Icc.mp hw.1, Finset.mem_Icc.mp hw.2, hh.2⟩
  have hparam (x : ℕ × ℕ) (hx : x ∈ S) :
      ∃ n : ℕ, x.1 = x₀.1 + B * n ∧ x.2 = x₀.2 + A * n := by
    apply exists_primeDilation_parameter hB hcop (hmin x hx)
    have h1 := (hdata x hx).2.2.2.2.2.2
    have h0 := (hdata x₀ hx₀).2.2.2.2.2.2
    exact_mod_cast (show (A : ℤ) * x.1 + B * x₀.2 = A * x₀.1 + B * x.2 by linarith only [h1, h0])
  let φ : ℕ × ℕ → ℕ := fun x => if hx : x ∈ S then Classical.choose (hparam x hx) else 0
  have hφ (x : ℕ × ℕ) (hx : x ∈ S) :
      x.1 = x₀.1 + B * φ x ∧ x.2 = x₀.2 + A * φ x := by
    dsimp only [φ]
    rw [dif_pos hx]
    exact Classical.choose_spec (hparam x hx)
  let F := (Finset.Icc 1 (P / B)).filter (fun n =>
    (B * n + x₀.1).Prime ∧ (A * n + x₀.2).Prime ∧ h < B * n + x₀.1 ∧ h < A * n + x₀.2)
  have hmaps (x : ℕ × ℕ) (hx : x ∈ S) : φ x ∈ insert 0 F := by
    by_cases hn : φ x = 0
    · simp only [hn, Finset.mem_insert, true_or]
    · apply Finset.mem_insert_of_mem
      apply Finset.mem_filter.mpr
      have hnP : φ x ≤ P / B := by
        apply (Nat.le_div_iff_mul_le hB).mpr
        have hxp := (hdata x hx).1.2
        have hxφ := (hφ x hx).1
        nlinarith only [hxp, hxφ]
      refine ⟨Finset.mem_Icc.mpr ⟨by omega, hnP⟩, ?_⟩
      have hx' := (hdata x hx).2.2
      have he1 : B * φ x + x₀.1 = x.1 := by rw [Nat.add_comm, ← (hφ x hx).1]
      have he2 : A * φ x + x₀.2 = x.2 := by rw [Nat.add_comm, ← (hφ x hx).2]
      rw [he1, he2]
      exact ⟨hx'.1, hx'.2.1, hx'.2.2.1, hx'.2.2.2.1⟩
  have hinj : Set.InjOn φ (S : Set (ℕ × ℕ)) := by
    intro x hx y hy hxy
    apply Prod.ext
    · rw [(hφ x hx).1, (hφ y hy).1, hxy]
    · rw [(hφ x hx).2, (hφ y hy).2, hxy]
  have hcard := Finset.card_le_card_of_injOn φ hmaps hinj
  have hcard' : (S.card : ℝ) ≤ 1 + (F.card : ℝ) := by
    have hc : S.card ≤ F.card + 1 := hcard.trans (Finset.card_insert_le _ _)
    exact_mod_cast (by omega : S.card ≤ 1 + F.card)
  exact ⟨x₀, hx₀, hcard'⟩

/-- Complete actual primitive dilation-pair count. Every pair is parametrized from a least
anchor; its discriminant becomes the literal shift. The single anchor and full sieve remainder
are retained, and no additive-pair bound is substituted for a dilation pair. -/
theorem card_primeDilationPairs_le (P Q : ℕ) {P₁ : ℕ} (hP₁ : 2 ≤ P₁) (h : ℕ)
    {A B : ℕ} (hA : 0 < A) (hB : 0 < B) (hcop : A.Coprime B) (v : ℤ)
    {z : ℝ} (hz : 1 ≤ z) :
    ((primeDilationPairs P Q A B h v).card : ℝ) ≤
      1 + (P / B : ℕ) / primeDilationBoundingSum P₁ h A B v z +
        ∑ e ∈ (affinePairPrimorial P₁ h B A).divisors,
          if (e : ℝ) ≤ z then (6 : ℝ) ^ e.primeFactors.card else 0 := by
  classical
  let S := primeDilationPairs P Q A B h v
  by_cases hne : S.Nonempty
  · obtain ⟨x₀, hx₀, hcard⟩ := exists_primeDilationPairs_anchor_bound P Q A B h hB hcop v hne
    have hx := (Finset.mem_filter.mp hx₀).2
    have hb := card_primeAffinePair_le (P / B) hP₁ h hB hA x₀.1 x₀.2 hz
    rw [primeDilationBoundingSum_eq hx.2.2.2.2 P₁ h z] at hb
    exact hcard.trans (by linarith only [hb])
  · have hS : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    change (S.card : ℝ) ≤ _
    rw [hS, Finset.card_empty, Nat.cast_zero]
    have hden := primeDilationBoundingSum_nonneg hP₁ h A B v z
    positivity

/-- The actual dilation equation has no pairs at a gcd-incompatible shift. -/
theorem primeDilationPairs_eq_empty_of_not_gcd_dvd (P Q A B h : ℕ) {v : ℤ}
    (hv : ¬ (Nat.gcd A B : ℤ) ∣ v) : primeDilationPairs P Q A B h v = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hxv := (Finset.mem_filter.mp hx).2
  have hA : (Nat.gcd A B : ℤ) ∣ (A : ℤ) := Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left A B)
  have hB : (Nat.gcd A B : ℤ) ∣ (B : ℤ) := Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right A B)
  have hd := dvd_sub (dvd_mul_of_dvd_left hA (x.1 : ℤ)) (dvd_mul_of_dvd_left hB (x.2 : ℤ))
  exact hv (hxv.2.2.2.2 ▸ hd)

/-- Gcd reduction retains exactly every prime pair and every finite cutoff. -/
theorem primeDilationPairs_gcd_eq (P Q : ℕ) {A B : ℕ} (hA : 0 < A) (h : ℕ) (w : ℤ) :
    primeDilationPairs P Q A B h ((Nat.gcd A B : ℤ) * w) =
      primeDilationPairs P Q (A / Nat.gcd A B) (B / Nat.gcd A B) h w := by
  have hg : 0 < Nat.gcd A B := Nat.gcd_pos_of_pos_left B hA
  have hAc : (Nat.gcd A B : ℤ) * ((A / Nat.gcd A B : ℕ) : ℤ) = A := by
    exact_mod_cast Nat.mul_div_cancel' (Nat.gcd_dvd_left A B)
  have hBc : (Nat.gcd A B : ℤ) * ((B / Nat.gcd A B : ℕ) : ℤ) = B := by
    exact_mod_cast Nat.mul_div_cancel' (Nat.gcd_dvd_right A B)
  have heq (p q : ℕ) :
      (A : ℤ) * p - (B : ℤ) * q = (Nat.gcd A B : ℤ) * w ↔
        ((A / Nat.gcd A B : ℕ) : ℤ) * p - ((B / Nat.gcd A B : ℕ) : ℤ) * q = w := by
    have hf : (A : ℤ) * p - (B : ℤ) * q = (Nat.gcd A B : ℤ) *
        (((A / Nat.gcd A B : ℕ) : ℤ) * p - ((B / Nat.gcd A B : ℕ) : ℤ) * q) := by
      rw [mul_sub, ← mul_assoc, hAc, ← mul_assoc, hBc]
    rw [hf]
    constructor
    · intro hh
      exact mul_left_cancel₀ (by exact_mod_cast hg.ne') hh
    · intro hh
      exact congrArg (fun x : ℤ => (Nat.gcd A B : ℤ) * x) hh
  ext x
  simp only [primeDilationPairs, Finset.mem_filter, heq]

/-- Actual complete dilation-pair sieve for arbitrary positive slopes at every compatible shift.
The reduced slopes and signed shift determine the exact denominator; the anchor and all
finite Selberg errors remain visible. Incompatible shifts have no pairs by the preceding theorem. -/
theorem card_primeDilationPairs_gcd_le (P Q : ℕ) {P₁ : ℕ} (hP₁ : 2 ≤ P₁) (h : ℕ)
    {A B : ℕ} (hA : 0 < A) (hB : 0 < B) (w : ℤ) {z : ℝ} (hz : 1 ≤ z) :
    let g := Nat.gcd A B
    let a := A / g
    let b := B / g
    ((primeDilationPairs P Q A B h ((g : ℤ) * w)).card : ℝ) ≤
      1 + (P / b : ℕ) / primeDilationBoundingSum P₁ h a b w z +
        ∑ e ∈ (affinePairPrimorial P₁ h b a).divisors,
          if (e : ℝ) ≤ z then (6 : ℝ) ^ e.primeFactors.card else 0 := by
  dsimp only
  rw [primeDilationPairs_gcd_eq P Q hA h w]
  have hg : 0 < Nat.gcd A B := Nat.gcd_pos_of_pos_left B hA
  exact card_primeDilationPairs_le P Q hP₁ h
    (Nat.div_pos (Nat.gcd_le_left B hA) hg)
    (Nat.div_pos (Nat.gcd_le_right A hB) hg)
    (Nat.coprime_div_gcd_div_gcd hg) w hz

end RHTower.Sieve
