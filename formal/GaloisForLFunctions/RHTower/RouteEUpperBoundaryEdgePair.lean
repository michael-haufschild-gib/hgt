import GaloisForLFunctions.RHTower.MobiusCoprimeHarmonicUniform

/-!
# A cutoff-faithful two-edge boundary cancellation in Route E

At the physical upper boundary, the fourth corner of a parity rectangle lies beyond
cutoff. The two surviving off-diagonal Gamma--Hankel entries with small endpoints
`d` and `2d` still have opposite Möbius signs. For every quotient `q ≥ 3`, including
composite quotients, their exact difference has an extra reciprocal `q` factor.
The entire selected boundary family has absolute mass at most one at exponent one.
This does not bound balanced primitive-ratio pairs or the full covariance.
-/

open Finset ArithmeticFunction
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Two literal oriented off-diagonal entries with common upper endpoint `q*d`. -/
def routeEUpperBoundaryEdgePair (q d : ℕ) : ℝ :=
  2 * mobiusRealCoefficient d * mobiusRealCoefficient (q * d) /
      (((d + q * d : ℕ) : ℝ)) +
    2 * mobiusRealCoefficient (2 * d) * mobiusRealCoefficient (q * d) /
      (((2 * d + q * d : ℕ) : ℝ))

theorem routeEUpperBoundaryEdgePair_eq
    {q d : ℕ} (hd : 1 ≤ d) (hodd : Odd d) (hsf : Squarefree d)
    (hcop : d.Coprime q) :
    routeEUpperBoundaryEdgePair q d =
      2 * mobiusRealCoefficient q /
        ((d : ℝ) * ((q : ℝ) + 1) * ((q : ℝ) + 2)) := by
  have hμd : mobiusRealCoefficient d ^ 2 = 1 := by
    have hne : moebius d ≠ 0 := moebius_ne_zero_iff_squarefree.mpr hsf
    rcases moebius_ne_zero_iff_eq_or.mp hne with hm | hm <;>
      simp [mobiusRealCoefficient, hm]
  have hμqd : mobiusRealCoefficient (q * d) =
      mobiusRealCoefficient q * mobiusRealCoefficient d := by
    unfold mobiusRealCoefficient
    rw [Sieve.moebius_mul_of_coprime hcop.symm]
    push_cast
    ring
  have hμ2d : mobiusRealCoefficient (2 * d) = -mobiusRealCoefficient d := by
    have hm2 : moebius 2 = -1 := by
      simpa using ArithmeticFunction.moebius_apply_prime Nat.prime_two
    unfold mobiusRealCoefficient
    rw [Sieve.moebius_mul_of_coprime hodd.coprime_two_left]
    rw [hm2]
    norm_num
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hq1 : (0 : ℝ) < (q : ℝ) + 1 := by positivity
  have hq2 : (0 : ℝ) < (q : ℝ) + 2 := by positivity
  unfold routeEUpperBoundaryEdgePair
  rw [hμqd, hμ2d]
  have hden1 : (((d + q * d : ℕ) : ℝ)) = (d : ℝ) * ((q : ℝ) + 1) := by
    push_cast; ring
  have hden2 : (((2 * d + q * d : ℕ) : ℝ)) = (d : ℝ) * ((q : ℝ) + 2) := by
    push_cast; ring
  rw [hden1, hden2]
  calc
    2 * mobiusRealCoefficient d *
          (mobiusRealCoefficient q * mobiusRealCoefficient d) /
          ((d : ℝ) * ((q : ℝ) + 1)) +
        2 * -mobiusRealCoefficient d *
          (mobiusRealCoefficient q * mobiusRealCoefficient d) /
          ((d : ℝ) * ((q : ℝ) + 2)) =
      2 * mobiusRealCoefficient q * mobiusRealCoefficient d ^ 2 /
          ((d : ℝ) * ((q : ℝ) + 1)) -
        2 * mobiusRealCoefficient q * mobiusRealCoefficient d ^ 2 /
          ((d : ℝ) * ((q : ℝ) + 2)) := by ring
    _ = _ := by rw [hμd]; field_simp; ring

private theorem sum_inv_upper_half_le_two (M : ℕ) :
    ∑ d ∈ (Finset.Icc 1 M).filter (fun d => M < 2 * d), (1 : ℝ) / d ≤ 2 := by
  let S := (Finset.Icc 1 M).filter (fun d => M < 2 * d)
  have hcard : S.card ≤ M := by
    have hsub : S ⊆ Finset.Icc 1 M := Finset.filter_subset _ _
    simpa [S] using Finset.card_le_card hsub
  have hterm : ∀ d ∈ S, (1 : ℝ) / d ≤ 2 / ((M : ℝ) + 1) := by
    intro d hdS
    have hd := Finset.mem_filter.mp hdS
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd.1).1
    have hbound : ((M : ℝ) + 1) ≤ 2 * (d : ℝ) := by
      exact_mod_cast hd.2
    apply (div_le_div_iff₀ hdpos (by positivity : (0 : ℝ) < (M : ℝ) + 1)).2
    nlinarith
  have h := Finset.sum_le_sum hterm
  have hsum : (∑ _d ∈ S, 2 / ((M : ℝ) + 1)) =
      (S.card : ℝ) * (2 / ((M : ℝ) + 1)) := by simp
  rw [hsum] at h
  have hcardR : (S.card : ℝ) ≤ M := by exact_mod_cast hcard
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  change (∑ d ∈ S, (1 : ℝ) / d) ≤ 2
  calc
    _ ≤ (S.card : ℝ) * (2 / ((M : ℝ) + 1)) := h
    _ ≤ (M : ℝ) * (2 / ((M : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_right hcardR (by positivity)
    _ ≤ 2 := by
      have hle : (M : ℝ) / ((M : ℝ) + 1) ≤ 1 :=
        (div_le_one (by positivity : (0 : ℝ) < (M : ℝ) + 1)).2 (by linarith)
      calc
        (M : ℝ) * (2 / ((M : ℝ) + 1)) =
            2 * ((M : ℝ) / ((M : ℝ) + 1)) := by ring
        _ ≤ 2 := by nlinarith

/-- Admitted odd squarefree cofactors on the physical upper boundary. -/
def routeEUpperBoundaryCofactors (N q : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (N / q)).filter
    (fun d => Odd d ∧ Squarefree d ∧ d.Coprime q ∧ N / q < 2 * d)

theorem routeEUpperBoundaryCofactors_physical
    {N q d : ℕ} (hq : 3 ≤ q) (hd : d ∈ routeEUpperBoundaryCofactors N q) :
    1 ≤ d ∧ d < 2 * d ∧ 2 * d < q * d ∧ q * d ≤ N ∧ N < 2 * (q * d) := by
  obtain ⟨hdi, _hodd, _hsf, _hcop, hupper⟩ := Finset.mem_filter.mp hd
  have hdlo : 1 ≤ d := (Finset.mem_Icc.mp hdi).1
  have hdhi : d ≤ N / q := (Finset.mem_Icc.mp hdi).2
  have hqpos : 0 < q := by omega
  have hcut : q * d ≤ N := by
    have := (Nat.le_div_iff_mul_le hqpos).mp hdhi
    simpa [Nat.mul_comm] using this
  have hhalf : N < 2 * (q * d) := by
    have := (Nat.div_lt_iff_lt_mul hqpos).mp hupper
    nlinarith
  refine ⟨hdlo, by omega, ?_, hcut, hhalf⟩
  nlinarith

theorem routeEUpperBoundaryNegativeEdge_injective
    {q₁ q₂ d₁ d₂ : ℕ} (hd₁ : 1 ≤ d₁)
    (h : (d₁, q₁ * d₁) = (d₂, q₂ * d₂)) :
    q₁ = q₂ ∧ d₁ = d₂ := by
  have hd : d₁ = d₂ := congrArg Prod.fst h
  subst d₂
  have hqd : q₁ * d₁ = q₂ * d₁ := congrArg Prod.snd h
  exact ⟨mul_right_cancel₀ (by omega : d₁ ≠ 0) hqd, rfl⟩

theorem routeEUpperBoundaryPositiveEdge_injective
    {q₁ q₂ d₁ d₂ : ℕ} (hd₁ : 1 ≤ d₁)
    (h : (2 * d₁, q₁ * d₁) = (2 * d₂, q₂ * d₂)) :
    q₁ = q₂ ∧ d₁ = d₂ := by
  have hfirst : 2 * d₁ = 2 * d₂ := congrArg Prod.fst h
  have hd : d₁ = d₂ := by omega
  subst d₂
  have hqd : q₁ * d₁ = q₂ * d₁ := congrArg Prod.snd h
  exact ⟨mul_right_cancel₀ (by omega : d₁ ≠ 0) hqd, rfl⟩

theorem routeEUpperBoundaryEdges_disjoint
    {q₁ q₂ d₁ d₂ : ℕ} (hodd : Odd d₁)
    (h : (d₁, q₁ * d₁) = (2 * d₂, q₂ * d₂)) : False := by
  have hfirst : d₁ = 2 * d₂ := congrArg Prod.fst h
  have heven : Even d₁ := ⟨d₂, by omega⟩
  exact (Nat.not_even_iff_odd.mpr hodd) heven

private theorem sum_inv_routeEUpperBoundaryCofactors_le_two (N q : ℕ) :
    ∑ d ∈ routeEUpperBoundaryCofactors N q, (1 : ℝ) / d ≤ 2 := by
  have hsub : routeEUpperBoundaryCofactors N q ⊆
      (Finset.Icc 1 (N / q)).filter (fun d => N / q < 2 * d) := by
    intro d hd
    simp only [routeEUpperBoundaryCofactors, Finset.mem_filter] at hd ⊢
    exact ⟨hd.1, hd.2.2.2.2⟩
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun d _ _ => by positivity)).trans
    (sum_inv_upper_half_le_two (N / q))

private theorem boundaryEdge_reciprocal_telescope (N : ℕ) (hN : 3 ≤ N) :
    (∑ q ∈ Finset.Icc 3 N,
      ((1 : ℝ) / ((q : ℝ) + 1) - 1 / ((q : ℝ) + 2))) =
      1 / 4 - 1 / ((N : ℝ) + 2) := by
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ N hN ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 3 ≤ N + 1), ih]
      push_cast
      ring

private theorem sum_reciprocal_product_le_quarter (N : ℕ) :
    (∑ q ∈ Finset.Icc 3 N,
      (1 : ℝ) / (((q : ℝ) + 1) * ((q : ℝ) + 2))) ≤ 1 / 4 := by
  by_cases hN : 3 ≤ N
  · have hsum := boundaryEdge_reciprocal_telescope N hN
    have hterm (q : ℕ) :
        (1 : ℝ) / (((q : ℝ) + 1) * ((q : ℝ) + 2)) =
          1 / ((q : ℝ) + 1) - 1 / ((q : ℝ) + 2) := by
      have hq1 : (0 : ℝ) < (q : ℝ) + 1 := by positivity
      have hq2 : (0 : ℝ) < (q : ℝ) + 2 := by positivity
      field_simp
      ring
    simp_rw [hterm] at hsum ⊢
    rw [hsum]
    have hlast : (0 : ℝ) ≤ 1 / ((N : ℝ) + 2) := by positivity
    linarith
  · have : N < 3 := by omega
    simp [Finset.Icc_eq_empty_of_lt this]

/-- The selected disjoint two-edge family in the literal order-one covariance. -/
def routeEUpperBoundaryPairedCovariance (N : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 3 N,
    ∑ d ∈ routeEUpperBoundaryCofactors N q, routeEUpperBoundaryEdgePair q d

theorem routeEUpperBoundaryPairedCovariance_eq (N : ℕ) :
    routeEUpperBoundaryPairedCovariance N =
      ∑ q ∈ Finset.Icc 3 N,
        ∑ d ∈ routeEUpperBoundaryCofactors N q,
          2 * mobiusRealCoefficient q /
            ((d : ℝ) * ((q : ℝ) + 1) * ((q : ℝ) + 2)) := by
  unfold routeEUpperBoundaryPairedCovariance
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro d hd
  obtain ⟨hdi, hodd, hsf, hcop, _hupper⟩ := Finset.mem_filter.mp hd
  exact routeEUpperBoundaryEdgePair_eq (Finset.mem_Icc.mp hdi).1 hodd hsf hcop

/-- Uniform cutoff-independent payment of the selected upper-boundary family. -/
theorem routeEUpperBoundaryPairedCovariance_abs_le_one (N : ℕ) :
    |routeEUpperBoundaryPairedCovariance N| ≤ 1 := by
  rw [routeEUpperBoundaryPairedCovariance_eq]
  calc
    |∑ q ∈ Finset.Icc 3 N,
        ∑ d ∈ routeEUpperBoundaryCofactors N q,
          2 * mobiusRealCoefficient q /
            ((d : ℝ) * ((q : ℝ) + 1) * ((q : ℝ) + 2))| ≤
      ∑ q ∈ Finset.Icc 3 N,
        ∑ d ∈ routeEUpperBoundaryCofactors N q,
          |2 * mobiusRealCoefficient q /
            ((d : ℝ) * ((q : ℝ) + 1) * ((q : ℝ) + 2))| := by
        calc
          _ ≤ ∑ q ∈ Finset.Icc 3 N,
              |∑ d ∈ routeEUpperBoundaryCofactors N q,
                2 * mobiusRealCoefficient q /
                  ((d : ℝ) * ((q : ℝ) + 1) * ((q : ℝ) + 2))| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ _ := Finset.sum_le_sum (fun q _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ q ∈ Finset.Icc 3 N,
          (2 / (((q : ℝ) + 1) * ((q : ℝ) + 2))) *
            (∑ d ∈ routeEUpperBoundaryCofactors N q, (1 : ℝ) / d) := by
      apply Finset.sum_le_sum
      intro q hq
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro d hd
      have hdpos : (0 : ℝ) < d := by
        exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1
      have hq1 : (0 : ℝ) < (q : ℝ) + 1 := by positivity
      have hq2 : (0 : ℝ) < (q : ℝ) + 2 := by positivity
      have hμ : |mobiusRealCoefficient q| ≤ 1 := by
        unfold mobiusRealCoefficient
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := q)
      have hden : 0 < (d : ℝ) * ((q : ℝ) + 1) * ((q : ℝ) + 2) :=
        mul_pos (mul_pos hdpos hq1) hq2
      have hnum : |2 * mobiusRealCoefficient q| ≤ 2 := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        nlinarith
      calc
        |2 * mobiusRealCoefficient q /
            ((d : ℝ) * ((q : ℝ) + 1) * ((q : ℝ) + 2))| =
          |2 * mobiusRealCoefficient q| /
            ((d : ℝ) * ((q : ℝ) + 1) * ((q : ℝ) + 2)) := by
              rw [abs_div, abs_of_pos hden]
        _ ≤ 2 / ((d : ℝ) * ((q : ℝ) + 1) * ((q : ℝ) + 2)) :=
          div_le_div_of_nonneg_right hnum hden.le
        _ = (2 / (((q : ℝ) + 1) * ((q : ℝ) + 2))) * ((1 : ℝ) / d) := by
          field_simp
    _ ≤ ∑ q ∈ Finset.Icc 3 N,
          4 / (((q : ℝ) + 1) * ((q : ℝ) + 2)) := by
      apply Finset.sum_le_sum
      intro q hq
      have hqden : 0 ≤ 2 / (((q : ℝ) + 1) * ((q : ℝ) + 2)) := by positivity
      calc
        _ ≤ (2 / (((q : ℝ) + 1) * ((q : ℝ) + 2))) * 2 :=
          mul_le_mul_of_nonneg_left (sum_inv_routeEUpperBoundaryCofactors_le_two N q) hqden
        _ = _ := by ring
    _ = 4 * ∑ q ∈ Finset.Icc 3 N,
          (1 : ℝ) / (((q : ℝ) + 1) * ((q : ℝ) + 2)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ ≤ 1 := by
      nlinarith [sum_reciprocal_product_le_quarter N]

end
end RHTower
