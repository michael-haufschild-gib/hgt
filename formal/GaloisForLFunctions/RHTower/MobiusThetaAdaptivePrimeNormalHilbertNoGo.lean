import GaloisForLFunctions.RHTower.MobiusThetaAdaptivePrimeNormalCodiagonal
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Hilbert-range no-go for the adaptive prime-normal codiagonal

The adaptive prime-normal codiagonal is bounded below on its infinite
`ell^(1 : ℕ)` prime source.  This file proves that its stability cannot survive
any bounded postcomparison into a complex inner-product space.

The quantitative mechanism is finite and unconditional.  Given finitely
many Hilbert vectors, signs can be chosen recursively using the
parallelogram law so that the signed sum has squared norm at most the sum of
the individual squared norms.  Therefore every bounded map
`T : ell^(1 : ℕ)(I) -> H` admits signed packets of `ell^(1 : ℕ)` norm `n` whose image
has norm at most `sqrt n * ||T||`.  For infinite `I`, no positive lower
modulus is possible.

Applied to the adaptive codiagonal, this rules out a bounded-below linear
identification of its closed `ell^(1 : ℕ)` source range with the Hilbertian
completed Xi/Green carrier.  Exact descent must change Banach geometry
before Hilbert polarization; a literal stable-range equality between these
two marginal completions cannot be the missing RH theorem.
-/

open Complex

namespace RHTower

noncomputable section

/-- Finite Hilbert sign selection: one signed sum has energy no larger than
the sum of the individual energies. -/
theorem exists_signs_norm_sq_sum_le
    {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (v : ι → H) (s : Finset ι) :
    ∃ ε : ι → ℂ,
      (∀ i ∈ s, ε i = 1 ∨ ε i = -1) ∧
      ‖∑ i ∈ s, ε i • v i‖ ^ 2 ≤ ∑ i ∈ s, ‖v i‖ ^ 2 := by
  classical
  induction s using Finset.induction with
  | empty =>
      refine ⟨fun _ => 1, ?_, ?_⟩
      · simp
      · simp
  | @insert a s ha ih =>
      rcases ih with ⟨ε, hε, hbound⟩
      let S : H := ∑ i ∈ s, ε i • v i
      let B : ℝ := ‖S‖ ^ 2 + ‖v a‖ ^ 2
      by_cases hplus : ‖v a + S‖ ^ 2 ≤ B
      · refine ⟨fun j => if j = a then 1 else ε j, ?_, ?_⟩
        · intro i hi
          rw [Finset.mem_insert] at hi
          rcases hi with rfl | hi
          · simp
          · have hia : i ≠ a := by
              intro h
              subst i
              exact ha hi
            simpa [hia] using hε i hi
        · have hsum :
              ∑ i ∈ insert a s, (if i = a then 1 else ε i) • v i =
                v a + S := by
            rw [Finset.sum_insert ha]
            simp only [if_pos, one_smul]
            congr 1
            apply Finset.sum_congr rfl
            intro i hi
            have hia : i ≠ a := by
              intro h
              subst i
              exact ha hi
            rw [if_neg hia]
          rw [hsum, Finset.sum_insert ha]
          dsimp only [B] at hplus
          linarith
      · refine ⟨fun j => if j = a then -1 else ε j, ?_, ?_⟩
        · intro i hi
          rw [Finset.mem_insert] at hi
          rcases hi with rfl | hi
          · simp
          · have hia : i ≠ a := by
              intro h
              subst i
              exact ha hi
            simpa [hia] using hε i hi
        · have hpara := parallelogram_law_with_norm ℂ (v a) S
          have hminus : ‖v a - S‖ ^ 2 ≤ B := by
            dsimp only [B] at hplus ⊢
            nlinarith
          have hsum :
              ∑ i ∈ insert a s, (if i = a then -1 else ε i) • v i =
                -(v a - S) := by
            rw [Finset.sum_insert ha]
            simp only [if_pos, neg_smul, one_smul]
            have hrest :
                ∑ i ∈ s, (if i = a then -1 else ε i) • v i = S := by
              apply Finset.sum_congr rfl
              intro i hi
              have hia : i ≠ a := by
                intro h
                subst i
                exact ha hi
              rw [if_neg hia]
            rw [hrest]
            abel
          rw [hsum, norm_neg, Finset.sum_insert ha]
          dsimp only [B] at hminus
          linarith

/-- Every finite coordinate set contains a signed `ell^(1 : ℕ)` packet whose
Hilbert image has only square-root growth. -/
theorem exists_lpOne_signed_packet_hilbert_bound
    {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : lp (fun _ : ι => ℂ) 1 →L[ℂ] H) (s : Finset ι) :
    ∃ x : lp (fun _ : ι => ℂ) 1,
      ‖x‖ = s.card ∧ ‖T x‖ ^ 2 ≤ s.card * ‖T‖ ^ 2 := by
  classical
  let e : ι → lp (fun _ : ι => ℂ) 1 := fun i =>
    lp.single (E := fun _ : ι => ℂ) 1 i 1
  obtain ⟨ε, hε, hsign⟩ := exists_signs_norm_sq_sum_le (fun i => T (e i)) s
  let x : lp (fun _ : ι => ℂ) 1 :=
    ∑ i ∈ s, lp.single (E := fun _ : ι => ℂ) 1 i (ε i)
  refine ⟨x, ?_, ?_⟩
  · have hnorm := lp.norm_sum_single (p := (1 : ENNReal))
      (by norm_num) (fun i => ε i) s
    simp only [ENNReal.toReal_one, Real.rpow_one] at hnorm
    calc
      ‖x‖ = ∑ i ∈ s, ‖ε i‖ := by simpa [x] using hnorm
      _ = ∑ _i ∈ s, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro i hi
        rcases hε i hi with hi1 | hi1 <;> rw [hi1] <;> norm_num
      _ = s.card := by simp
  · have hsingle : ∀ i : ι,
        lp.single (E := fun _ : ι => ℂ) 1 i (ε i) = ε i • e i := by
      intro i
      ext j
      by_cases hij : i = j
      · subst j
        simp [e, lp.single_apply]
      · simp [e, lp.single_apply, hij]
    have hTx : T x = ∑ i ∈ s, ε i • T (e i) := by
      simp_rw [x, hsingle, map_sum, map_smul]
    rw [hTx]
    calc
      ‖∑ i ∈ s, ε i • T (e i)‖ ^ 2 ≤
          ∑ i ∈ s, ‖T (e i)‖ ^ 2 := hsign
      _ ≤ ∑ _i ∈ s, ‖T‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        have hTi := T.le_opNorm (e i)
        rw [show ‖e i‖ = 1 by simp [e, lp.norm_single]] at hTi
        simpa only [mul_one] using
          pow_le_pow_left₀ (norm_nonneg _) hTi 2
      _ = s.card * ‖T‖ ^ 2 := by simp

/-- Infinite `ell^(1 : ℕ)` has no positive-lower-modulus linear map into a
complex inner-product space. -/
theorem lpOne_to_innerProduct_not_boundedBelow
    {H ι : Type*} [Infinite ι]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : lp (fun _ : ι => ℂ) 1 →L[ℂ] H) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ x, c * ‖x‖ ≤ ‖T x‖ := by
  rintro ⟨c, hc, hlower⟩
  let emb : ℕ ↪ ι := Infinite.natEmbedding ι
  obtain ⟨n : ℕ, hn⟩ := exists_nat_gt (‖T‖ ^ 2 / c ^ 2)
  let s : Finset ι := (Finset.range n).map emb
  obtain ⟨x, hxnorm, hupper⟩ :=
    exists_lpOne_signed_packet_hilbert_bound T s
  have hcard : s.card = n := by simp [s]
  have hnpos : (0 : ℝ) < n := by
    have hnonneg : 0 ≤ ‖T‖ ^ 2 / c ^ 2 := by positivity
    exact_mod_cast lt_of_le_of_lt hnonneg hn
  have hlower' := hlower x
  have hsquare : (c * ‖x‖) ^ 2 ≤ ‖T x‖ ^ 2 := by
    have hleft : 0 ≤ c * ‖x‖ := mul_nonneg hc.le (norm_nonneg _)
    exact pow_le_pow_left₀ hleft hlower' 2
  rw [hxnorm, hcard] at hsquare
  rw [hcard] at hupper
  have hratio : (‖T‖ ^ 2 : ℝ) < (n : ℝ) * c ^ 2 := by
    have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc
    exact (div_lt_iff₀ hc2).mp hn
  nlinarith

/-- Any bounded Hilbert postcomparison destroys the adaptive source's
positive lower modulus. -/
theorem adaptivePrimeNormalCodiagonal_no_bounded_hilbert_postcomparison
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (N : ℕ) (w : ℂ)
    (hNw : (1 / 2 : ℝ) ≤
      (N : ℝ) * (mobiusThetaCenteredParameter w).re)
    (J : AdaptiveArithmeticL1 →L[ℂ] H) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ x : AdaptivePrimeL1,
      c * ‖x‖ ≤ ‖J (adaptivePrimeNormalCodiagonal N w hNw x)‖ := by
  exact lpOne_to_innerProduct_not_boundedBelow
    (J.comp (adaptivePrimeNormalCodiagonal N w hNw))

end

end RHTower
