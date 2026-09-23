import GaloisForLFunctions.RHTower.Sieve.MarkerBadCount

/-!
# Markers lost to bad starts, without the multiplicity loss

`RHTower.card_markers_start_mem_le` discards `#S · (X/(A(A+1)) + 1)` markers for a set `S` of bad
starts — the number of bad starts times the *largest* reciprocal fibre.  At the marker scale `√X`
the fibre size is `O(1)` and the markers are `1/log X`-sparse inside it, so that estimate throws
away a factor `log X`.

Replacing the largest fibre by the *mean square* of the fibre size removes exactly that factor.  The
mean square is the marker count plus twice a shifted-pair count
(`Sieve/FibreMultiplicitySecondMoment`), and a Cauchy--Schwarz gives

```text
    #{p ∈ M : X/p ∈ S}²  ≤  #S · ( #M + 2·(shifted-pair budget) ) ,
```

so a bad-start density `ρ` costs a `√ρ` fraction of the markers rather than `ρ·log X`.
-/

namespace RHTower.Sieve

open Finset

/-- **Separation for the reciprocal start map.**  Two integers with the same reciprocal start above
`A` differ by at most `X/A²`. -/
theorem reciprocal_separation {X A p q : ℕ} (hA : 1 ≤ A) (hp : 0 < p)
    (hpq : p < q) (hAt : A ≤ X / p) (heq : X / q = X / p) :
    q ≤ p + X / (A * A) := by
  set t : ℕ := X / p with ht
  have htq : t * q ≤ X := by
    have h := Nat.div_mul_le_self X q
    rw [heq] at h
    calc t * q = X / p * q := by rw [ht]
      _ ≤ X := h
  have htp : t * p ≤ X := by
    have h := Nat.div_mul_le_self X p
    calc t * p = X / p * p := by rw [ht]
      _ ≤ X := h
  have hlt : X < (t + 1) * p := by
    have : X / p < t + 1 := by omega
    exact (Nat.div_lt_iff_lt_mul hp).1 this
  have hstep : t * (q - p) < p := by
    have h1 : t * q < (t + 1) * p := lt_of_le_of_lt htq hlt
    have h2 : t * q = t * p + t * (q - p) := by
      rw [← Nat.mul_add]
      congr 1
      omega
    have h3 : (t + 1) * p = t * p + p := by ring
    omega
  have hsq : (A * A) * (q - p) ≤ X := by
    have hAt' : A ≤ t := hAt
    calc (A * A) * (q - p) ≤ (t * t) * (q - p) := by
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul hAt' hAt')
      _ = t * (t * (q - p)) := by ring
      _ ≤ t * p := Nat.mul_le_mul_left t (le_of_lt hstep)
      _ ≤ X := htp
  have hdiv : q - p ≤ X / (A * A) := by
    refine (Nat.le_div_iff_mul_le (by positivity)).2 ?_
    rw [mul_comm]
    exact hsq
  omega

/-- **The device bound on lost markers.** -/
theorem sq_card_markers_start_mem_le {X : ℕ} {M S : Finset ℕ} {K : ℕ} {Pi : ℝ}
    (hsep : ∀ p ∈ M, ∀ q ∈ M, p < q → X / q = X / p → q ≤ p + K)
    (hpair : ∑ d ∈ Finset.Icc 1 K, (((M.filter (fun p => p + d ∈ M)).card : ℕ) : ℝ) ≤ Pi) :
    (((M.filter (fun p => X / p ∈ S)).card : ℕ) : ℝ) ^ (2 : ℕ)
      ≤ (S.card : ℝ) * ((M.card : ℝ) + 2 * Pi) := by
  classical
  set f : ℕ → ℕ := fun p => X / p with hf
  set B : Finset ℕ := S ∩ M.image f with hB
  have hBsub : B ⊆ M.image f := Finset.inter_subset_right
  have hfilter : M.filter (fun p => X / p ∈ S) = M.filter (fun p => f p ∈ B) := by
    ext p
    rw [Finset.mem_filter, Finset.mem_filter, hB, Finset.mem_inter]
    constructor
    · rintro ⟨hpM, hpS⟩
      exact ⟨hpM, hpS, Finset.mem_image_of_mem f hpM⟩
    · rintro ⟨hpM, hpS, -⟩
      exact ⟨hpM, hpS⟩
  have hsep' : ∀ p ∈ M, ∀ q ∈ M, p < q → f q = f p → q ≤ p + K := hsep
  have hmain := sq_card_marker_bad_le (S := M) (B := B) f K hBsub hsep' hpair
  rw [hfilter]
  refine hmain.trans (mul_le_mul_of_nonneg_right ?_ ?_)
  · exact Nat.cast_le.2 (Finset.card_le_card (Finset.inter_subset_left))
  · have hM0 : (0 : ℝ) ≤ (M.card : ℝ) := Nat.cast_nonneg _
    have hPi : (0 : ℝ) ≤ Pi := by
      refine le_trans ?_ hpair
      exact Finset.sum_nonneg fun d _ => Nat.cast_nonneg _
    linarith

end RHTower.Sieve
