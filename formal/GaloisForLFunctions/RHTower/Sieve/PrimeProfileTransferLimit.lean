import GaloisForLFunctions.RHTower.Sieve.PrimeProfileIntegralBound

/-!
# The prime-profile transfer

Reading a prime `p ≤ N` at its exponent `t_p = log p / log N` and sampling a profile there, the
reciprocal prime measure converges to `dt/t`:

`Σ_{p ≤ N} g (log p / log N) / p  ⟶  ∫₀¹ g(t) dt/t`

for every Lipschitz profile vanishing linearly at the origin.

The proof is the explicit master bound of the previous file, read at a fixed cell count `m`.  As
`N → ∞` the window masses converge to the cell weights and the Mertens error dies, leaving
`2(L/m)·log m + 2C/m`; that vanishes as `m → ∞` because `log m / m → 0`.  Both hypotheses are
satisfied by the card's profile class `g = (e^f − 1)²` with `f ∈ C¹([0,1])`, `f(0) = 0`.
-/

namespace RHTower.Sieve

open Filter Finset
open scoped Topology

noncomputable section

/-! ## The cell-count error vanishes -/

theorem tendsto_log_div_natCast : Tendsto (fun m : ℕ => Real.log m / m) atTop (𝓝 0) :=
  (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero).comp tendsto_natCast_atTop_atTop

/-- The total cell error `2L·log m/m + 2C/m` vanishes with the cell count. -/
theorem tendsto_cellError (L C : ℝ) :
    Tendsto (fun m : ℕ => 2 * L * (Real.log m / m) + 2 * C * (1 / (m : ℝ))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun m : ℕ => 2 * L * (Real.log m / m)) atTop (𝓝 0) := by
    simpa using tendsto_log_div_natCast.const_mul (2 * L)
  have h2 : Tendsto (fun m : ℕ => 2 * C * (1 / (m : ℝ))) atTop (𝓝 0) := by
    have hinv : Tendsto (fun m : ℕ => 1 / (m : ℝ)) atTop (𝓝 0) :=
      Tendsto.div_atTop tendsto_const_nhds tendsto_natCast_atTop_atTop
    simpa using hinv.const_mul (2 * C)
  simpa using h1.add h2

/-! ## The `N`-limit at a fixed cell count -/

theorem tendsto_exponentWindowMass {m : ℕ} (hm : 1 ≤ m) {j : ℕ} (hj : 1 ≤ j) :
    Tendsto (fun N : ℕ => exponentWindowMass m N j) atTop
      (𝓝 (Real.log ((j : ℝ) + 1) - Real.log j)) := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  have ha : (0 : ℝ) < (j : ℝ) / m := by positivity
  have hab : (j : ℝ) / m ≤ ((j : ℝ) + 1) / m := cellLeft_le_right (m := m) (j := j) hm
  have h := tendsto_sum_inv_exponentWindow ha hab
  have hval : Real.log (((j : ℝ) + 1) / m) - Real.log ((j : ℝ) / m)
      = Real.log ((j : ℝ) + 1) - Real.log j := by
    rw [Real.log_div (by linarith) (ne_of_gt hmpos),
      Real.log_div (ne_of_gt hjpos) (ne_of_gt hmpos)]
    ring
  rw [hval] at h
  exact h

/-- At a fixed cell count the whole `N`-dependent error converges to `2(L/m)·log m + 2C/m`. -/
theorem tendsto_profileErrorBound {g : ℝ → ℝ} (L C : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun N : ℕ =>
        L / m * (∑ j ∈ Finset.Ico 1 m, exponentWindowMass m N j)
          + (C * ((1 : ℝ) / m) + C * mertensFirstConst / Real.log N)
          + (∑ j ∈ Finset.Ico 1 m,
              |g ((j : ℝ) / m)| *
                |exponentWindowMass m N j - (Real.log ((j : ℝ) + 1) - Real.log j)|)
          + L / m * Real.log m
          + C * ((1 : ℝ) / m))
      atTop
      (𝓝 (2 * L * (Real.log m / m) + 2 * C * (1 / (m : ℝ)))) := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hmass : Tendsto (fun N : ℕ => ∑ j ∈ Finset.Ico 1 m, exponentWindowMass m N j) atTop
      (𝓝 (∑ j ∈ Finset.Ico 1 m, (Real.log ((j : ℝ) + 1) - Real.log j))) := by
    refine tendsto_finsetSum _ ?_
    intro j hj
    exact tendsto_exponentWindowMass hm (Finset.mem_Ico.1 hj).1
  rw [sum_Ico_log_increment hm] at hmass
  have hdev : Tendsto (fun N : ℕ =>
      ∑ j ∈ Finset.Ico 1 m,
        |g ((j : ℝ) / m)| *
          |exponentWindowMass m N j - (Real.log ((j : ℝ) + 1) - Real.log j)|)
      atTop (𝓝 0) := by
    have hzero : Tendsto (fun N : ℕ =>
        ∑ j ∈ Finset.Ico 1 m,
          |g ((j : ℝ) / m)| *
            |exponentWindowMass m N j - (Real.log ((j : ℝ) + 1) - Real.log j)|)
        atTop (𝓝 (∑ j ∈ Finset.Ico 1 m, |g ((j : ℝ) / m)| * (0 : ℝ))) := by
      refine tendsto_finsetSum _ ?_
      intro j hj
      refine Tendsto.const_mul _ ?_
      have hj1 := (Finset.mem_Ico.1 hj).1
      have hlim := tendsto_exponentWindowMass hm hj1
      have hsub := hlim.sub (tendsto_const_nhds
        (x := Real.log ((j : ℝ) + 1) - Real.log j) (f := (atTop : Filter ℕ)))
      rw [sub_self] at hsub
      simpa using hsub.abs
    simpa using hzero
  have hmert : Tendsto (fun N : ℕ => C * mertensFirstConst / Real.log N) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds tendsto_log_natCast_atTop'
  have hsum := (((hmass.const_mul (L / m)).add
    ((tendsto_const_nhds (x := C * ((1 : ℝ) / m))).add hmert)).add hdev).add
    (tendsto_const_nhds (x := L / m * Real.log m))
  have hfinal := hsum.add (tendsto_const_nhds (x := C * ((1 : ℝ) / m)))
  rw [show (L / (m : ℝ) * Real.log m + (C * ((1 : ℝ) / (m : ℝ)) + 0) + 0
      + L / (m : ℝ) * Real.log m + C * ((1 : ℝ) / (m : ℝ)))
      = 2 * L * (Real.log m / m) + 2 * C * (1 / (m : ℝ)) from by ring] at hfinal
  exact hfinal

/-! ## The transfer -/

/-- **The prime-profile transfer.**  For a Lipschitz profile vanishing linearly at the origin, the
prime reciprocal sum read in the exponent coordinate converges to `∫₀¹ g(t) dt/t`. -/
theorem tendsto_primeProfileSum
    {g : ℝ → ℝ} {L C : ℝ} (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hg : Continuous g) (hlip : ∀ s t : ℝ, |g s - g t| ≤ L * |s - t|)
    (hbd : ∀ t : ℝ, 0 ≤ t → |g t| ≤ C * t) :
    Tendsto (fun N : ℕ => primeProfileSum g N) atTop (𝓝 (∫ t in (0 : ℝ)..1, g t / t)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hhalf : 0 < ε / 2 := by linarith
  obtain ⟨m, hm1, hmsmall⟩ : ∃ m : ℕ, 1 ≤ m ∧
      2 * L * (Real.log m / m) + 2 * C * (1 / (m : ℝ)) < ε / 2 := by
    have hev := (tendsto_cellError L C).eventually_lt_const hhalf
    obtain ⟨M, hM⟩ := (hev.and (eventually_ge_atTop 1)).exists
    exact ⟨M, hM.2, hM.1⟩
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  have hrpos : (0 : ℝ) < (1 : ℝ) / (m : ℝ) := by positivity
  have hbound := tendsto_profileErrorBound (g := g) L C hm1
  have hlt := hbound.eventually_lt_const hmsmall
  obtain ⟨M, hM⟩ := eventually_atTop.1 ((hlt.and (eventually_le_rpow_natCast hrpos 2)).and
    (eventually_ge_atTop 2))
  refine ⟨M, fun N hN => ?_⟩
  obtain ⟨⟨hErr, hcut⟩, hN2⟩ := hM N hN
  have hmaster := abs_primeProfileSum_sub_integral_le hL hC hg hlip hbd hm1 hN2 hcut
  rw [Real.dist_eq]
  calc |primeProfileSum g N - ∫ t in (0 : ℝ)..1, g t / t| ≤ _ := hmaster
    _ < ε / 2 := hErr
    _ < ε := by linarith

end

end RHTower.Sieve
