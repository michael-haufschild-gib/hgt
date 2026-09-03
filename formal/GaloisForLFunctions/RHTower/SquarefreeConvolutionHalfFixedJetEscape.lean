import GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfFirstJetCountertermNoGo

/-!
# Escape of every fixed exponentially dressed arithmetic jet

Let `D_N` be the squarefree convolution-half Dirichlet polynomial and `b = 6/11`.  For each
fixed derivative order `k`, this module expands the `k`-jet at `b` of

```text
exp(N(s-b)) D_N(s).
```

The top Leibniz term is `N^k D_N(b)`.  Every remaining term contains a positive derivative of
`D_N`; Cauchy's estimate bounds those derivatives by explicit constants times `N`.  Their finite
sum is therefore at most `C_k N^k`.  Since `D_N(b)` has no bounded tail, every fixed dressed jet
has no bounded tail either.

This is the arithmetic obstruction behind all fixed-depth Hermite anchors.  A successor must let
jet depth grow with cutoff or abandon point-jet interpolation for distributed transition control.
-/

open Complex Filter Metric Set Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

def boundaryPositiveExponentialSeparator (N : ℕ) (s : ℂ) : ℂ :=
  Complex.exp ((N : ℂ) * (s - boundaryExteriorPoint))

def boundaryPositiveExponentialDress (N : ℕ) (s : ℂ) : ℂ :=
  boundaryPositiveExponentialSeparator N s * squarefreeHalfDirichletPartialSum N s

theorem analytic_boundaryPositiveExponentialSeparator (N : ℕ) :
    AnalyticOnNhd ℂ (boundaryPositiveExponentialSeparator N) Set.univ := by
  intro s _
  exact (analyticAt_const.mul (analyticAt_id.sub analyticAt_const)).cexp

@[simp] theorem boundaryPositiveExponentialSeparator_at_boundary (N : ℕ) :
    boundaryPositiveExponentialSeparator N boundaryExteriorPoint = 1 := by
  simp [boundaryPositiveExponentialSeparator]

theorem hasDerivAt_boundaryPositiveExponentialSeparator (N : ℕ) (s : ℂ) :
    HasDerivAt (boundaryPositiveExponentialSeparator N)
      ((N : ℂ) * boundaryPositiveExponentialSeparator N s) s := by
  change HasDerivAt
    (fun z : ℂ => Complex.exp ((N : ℂ) * (z - boundaryExteriorPoint)))
    ((N : ℂ) * Complex.exp ((N : ℂ) * (s - boundaryExteriorPoint))) s
  have hinner :=
    (((hasDerivAt_id' s).sub_const boundaryExteriorPoint).const_mul (N : ℂ)).cexp
  apply hinner.congr_deriv
  ring

theorem iteratedDeriv_boundaryPositiveExponentialSeparator (N k : ℕ) :
    iteratedDeriv k (boundaryPositiveExponentialSeparator N) =
      fun s => (N : ℂ) ^ k * boundaryPositiveExponentialSeparator N s := by
  induction k with
  | zero => simp [iteratedDeriv_zero]
  | succ k ih =>
      rw [iteratedDeriv_succ, ih]
      funext s
      rw [deriv_const_mul _
        (hasDerivAt_boundaryPositiveExponentialSeparator N s).differentiableAt,
        (hasDerivAt_boundaryPositiveExponentialSeparator N s).deriv]
      ring

theorem iteratedDeriv_boundaryPositiveExponentialDress (N k : ℕ) :
    iteratedDeriv k (boundaryPositiveExponentialDress N) boundaryExteriorPoint =
      ∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℂ) * (N : ℂ) ^ i *
          iteratedDeriv (k - i) (squarefreeHalfDirichletPartialSum N)
            boundaryExteriorPoint := by
  have hE : ContDiffAt ℂ k (boundaryPositiveExponentialSeparator N)
      boundaryExteriorPoint :=
    ((analytic_boundaryPositiveExponentialSeparator N) boundaryExteriorPoint
      (Set.mem_univ _)).contDiffAt
  have hD : ContDiffAt ℂ k (squarefreeHalfDirichletPartialSum N)
      boundaryExteriorPoint :=
    ((analyticOnNhd_squarefreeHalfDirichletPartialSum N) boundaryExteriorPoint
      (Set.mem_univ _)).contDiffAt
  change iteratedDeriv k
    (boundaryPositiveExponentialSeparator N * squarefreeHalfDirichletPartialSum N)
    boundaryExteriorPoint = _
  rw [iteratedDeriv_mul hE hD]
  apply Finset.sum_congr rfl
  intro i hi
  rw [iteratedDeriv_boundaryPositiveExponentialSeparator]
  change (k.choose i : ℂ) *
    ((N : ℂ) ^ i * boundaryPositiveExponentialSeparator N boundaryExteriorPoint) * _ = _
  rw [boundaryPositiveExponentialSeparator_at_boundary, mul_one]

theorem norm_iteratedDeriv_squarefreeHalfDirichletPartialSum_boundary_le_mul_pow
    (j N : ℕ) :
    ‖iteratedDeriv j (squarefreeHalfDirichletPartialSum N) boundaryExteriorPoint‖ ≤
      (j.factorial : ℝ) * (N : ℝ) * 22 ^ j := by
  have h := norm_iteratedDeriv_squarefreeHalfDirichletPartialSum_boundary_le j N
  calc
    _ ≤ (j.factorial : ℝ) * (N : ℝ) / (1 / 22 : ℝ) ^ j := h
    _ = (j.factorial : ℝ) * (N : ℝ) * 22 ^ j := by
      rw [one_div_pow, one_div, div_inv_eq_mul]

def boundaryFixedJetRemainderBound (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k,
    (k.choose i : ℝ) * ((k - i).factorial : ℝ) * 22 ^ (k - i)

theorem boundaryFixedJetRemainderBound_nonneg (k : ℕ) :
    0 ≤ boundaryFixedJetRemainderBound k := by
  exact Finset.sum_nonneg fun i _ => by positivity

theorem norm_boundaryFixedJetRemainder_le
    (k N : ℕ) (hN : 1 ≤ N) :
    ‖∑ i ∈ Finset.range k,
        (k.choose i : ℂ) * (N : ℂ) ^ i *
          iteratedDeriv (k - i) (squarefreeHalfDirichletPartialSum N)
            boundaryExteriorPoint‖ ≤
      boundaryFixedJetRemainderBound k * (N : ℝ) ^ k := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  calc
    ‖∑ i ∈ Finset.range k,
        (k.choose i : ℂ) * (N : ℂ) ^ i *
          iteratedDeriv (k - i) (squarefreeHalfDirichletPartialSum N)
            boundaryExteriorPoint‖ ≤
        ∑ i ∈ Finset.range k,
          ‖(k.choose i : ℂ) * (N : ℂ) ^ i *
            iteratedDeriv (k - i) (squarefreeHalfDirichletPartialSum N)
              boundaryExteriorPoint‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range k,
        ((k.choose i : ℝ) * ((k - i).factorial : ℝ) * 22 ^ (k - i)) *
          (N : ℝ) ^ k := by
      apply Finset.sum_le_sum
      intro i hi
      have hik : i < k := Finset.mem_range.mp hi
      have hpow : (N : ℝ) ^ (i + 1) ≤ (N : ℝ) ^ k :=
        pow_le_pow_right₀ hNr (by omega)
      have hjet := norm_iteratedDeriv_squarefreeHalfDirichletPartialSum_boundary_le_mul_pow
        (k - i) N
      rw [norm_mul, norm_mul, Complex.norm_natCast, norm_pow, norm_natCast]
      calc
        (k.choose i : ℝ) * (N : ℝ) ^ i *
            ‖iteratedDeriv (k - i) (squarefreeHalfDirichletPartialSum N)
              boundaryExteriorPoint‖ ≤
            (k.choose i : ℝ) * (N : ℝ) ^ i *
              (((k - i).factorial : ℝ) * (N : ℝ) * 22 ^ (k - i)) := by
          gcongr
        _ = ((k.choose i : ℝ) * ((k - i).factorial : ℝ) * 22 ^ (k - i)) *
            (N : ℝ) ^ (i + 1) := by rw [pow_succ]; ring
        _ ≤ ((k.choose i : ℝ) * ((k - i).factorial : ℝ) * 22 ^ (k - i)) *
            (N : ℝ) ^ k := mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = boundaryFixedJetRemainderBound k * (N : ℝ) ^ k := by
      rw [boundaryFixedJetRemainderBound, Finset.sum_mul]

theorem iteratedDeriv_boundaryPositiveExponentialDress_eq_remainder_add
    (k N : ℕ) :
    iteratedDeriv k (boundaryPositiveExponentialDress N) boundaryExteriorPoint =
      (∑ i ∈ Finset.range k,
        (k.choose i : ℂ) * (N : ℂ) ^ i *
          iteratedDeriv (k - i) (squarefreeHalfDirichletPartialSum N)
            boundaryExteriorPoint) +
      (N : ℂ) ^ k * squarefreeHalfDirichletPartialSum N boundaryExteriorPoint := by
  rw [iteratedDeriv_boundaryPositiveExponentialDress, Finset.sum_range_succ]
  simp

private theorem exists_large_squarefreeHalfDirichletPartialSum_boundary_fixedJet
    (B : ℝ) (M : ℕ) :
    ∃ N : ℕ, M ≤ N ∧ B <
      ‖squarefreeHalfDirichletPartialSum N boundaryExteriorPoint‖ := by
  by_contra h
  push Not at h
  exact not_eventually_bounded_squarefreeHalfDirichletPartialSum_boundaryExteriorPoint
    ⟨B, M, fun N hMN => h N hMN⟩

theorem not_eventually_bounded_boundaryPositiveExponentialDress_jet
    (k : ℕ) :
    ¬ ∃ B : ℝ, ∃ M : ℕ, ∀ N : ℕ, M ≤ N →
      ‖iteratedDeriv k (boundaryPositiveExponentialDress N) boundaryExteriorPoint‖ ≤ B := by
  rintro ⟨B, M, hB⟩
  obtain ⟨N, hN, hraw⟩ :=
    exists_large_squarefreeHalfDirichletPartialSum_boundary_fixedJet
      (boundaryFixedJetRemainderBound k + B + 1) (max M 1)
  have hNM : M ≤ N := (le_max_left M 1).trans hN
  have hN1 : 1 ≤ N := (le_max_right M 1).trans hN
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  let R : ℂ := ∑ i ∈ Finset.range k,
    (k.choose i : ℂ) * (N : ℂ) ^ i *
      iteratedDeriv (k - i) (squarefreeHalfDirichletPartialSum N)
        boundaryExteriorPoint
  let D : ℂ := squarefreeHalfDirichletPartialSum N boundaryExteriorPoint
  have hR : ‖R‖ ≤ boundaryFixedJetRemainderBound k * (N : ℝ) ^ k :=
    norm_boundaryFixedJetRemainder_le k N hN1
  have hreverse : (N : ℝ) ^ k * ‖D‖ - ‖R‖ ≤
      ‖R + (N : ℂ) ^ k * D‖ := by
    have h := norm_sub_norm_le ((N : ℂ) ^ k * D) (-R)
    rw [norm_mul, norm_pow, norm_natCast, norm_neg, sub_neg_eq_add, add_comm] at h
    exact h
  have hjet : B < ‖R + (N : ℂ) ^ k * D‖ := by
    have hC : 0 ≤ boundaryFixedJetRemainderBound k :=
      boundaryFixedJetRemainderBound_nonneg k
    have hpow : (1 : ℝ) ≤ (N : ℝ) ^ k := one_le_pow₀ hNr
    have hbase : (N : ℝ) ^ k * ‖D‖ -
        boundaryFixedJetRemainderBound k * (N : ℝ) ^ k ≤
        ‖R + (N : ℂ) ^ k * D‖ :=
      (sub_le_sub_left hR ((N : ℝ) ^ k * ‖D‖)).trans hreverse
    calc
      B < (N : ℝ) ^ k *
          (boundaryFixedJetRemainderBound k + B + 1) -
          boundaryFixedJetRemainderBound k * (N : ℝ) ^ k := by
        have hBnonneg : 0 ≤ B := (norm_nonneg _).trans (hB (max M 1) (le_max_left M 1))
        nlinarith [mul_le_mul_of_nonneg_left hpow
          (add_nonneg (add_nonneg hC hBnonneg) zero_le_one)]
      _ < (N : ℝ) ^ k * ‖D‖ -
          boundaryFixedJetRemainderBound k * (N : ℝ) ^ k := by
        have hp : 0 < (N : ℝ) ^ k := pow_pos (by positivity) _
        nlinarith [mul_lt_mul_of_pos_left hraw hp]
      _ ≤ ‖R + (N : ℂ) ^ k * D‖ := hbase
  have heq := iteratedDeriv_boundaryPositiveExponentialDress_eq_remainder_add k N
  change iteratedDeriv k (boundaryPositiveExponentialDress N) boundaryExteriorPoint =
    R + (N : ℂ) ^ k * D at heq
  have hBN := hB N hNM
  rw [heq] at hBN
  exact (not_lt_of_ge hBN) hjet

end

end RHTower

