import GaloisForLFunctions.RHTower.RelaxedHerglotzProducerFloor

/-!
# Relaxed producers converge to the von Mangoldt weights

A log-bounded weight sequence `lam` is a Herglotz producer on `Re s > σ₀`
(`IsHerglotzProducerOn σ₀ lam`) when `½ψ(s/2) − ½log π + 1/s + 1/(s−1) − Σ lam(n) n^{−s}` continues
holomorphically to `Re s > σ₀` with nonnegative real part.  On `Re s > ½` the only producer is `Λ`
(and it exists iff RH); on `Re s > ½ + δ` there may be many.

**Theorem** (`abs_sub_vonMangoldt_lt_of_isHerglotzProducerOn`).  For every `n` and every `ε > 0`
there is `δ₀ > 0` such that every log-bounded producer on `Re s > ½ + δ` with `0 < δ < δ₀` satisfies
`|lam(n) − Λ(n)| < ε`.  So the relaxed producer sets shrink to `{Λ}` in the product topology as the
level approaches the critical line.  The statement is unconditional; it is vacuous for small `δ`
when RH fails, since then no producers exist close to the line.

The proof uses the sequential closedness of producer levels (`isHerglotzProducerOn_of_tendsto`): a
pointwise limit of log-bounded producers on `Re s > σ₀ + 1/(k+2)` is a producer on `Re s > σ₀`.

Proof of the theorem.  Suppose producers `lam_k` on `Re s > ½ + δ_k`, with `δ_k < 1/(k+2)`, stay at
distance `≥ ε` from `Λ(n)`.  A subsequence converges pointwise in the compact box
`∏[−log m, log m]`.  Its limit is a producer on `Re s > ½`, hence equals `Λ` by uniqueness
(`herglotzProducer_eq_vonMangoldt`), but it stays at distance `≥ ε` from `Λ(n)`.

Reading: constructing producers close to the critical line is constructing the primes.  Any family
of relaxed producers whose levels tend to `½` has weights tending to `Λ`.
-/

open Complex Filter Topology Set Metric

noncomputable section

namespace RHTower.RelaxedHerglotz

open RHTower.AtomDomination GaloisForLFunctions.HTGeometry

/-- **Relaxed producers converge to `Λ`.**  For every `n` and `ε > 0` there is `δ₀ > 0` such that
every log-bounded Herglotz producer on `Re s > ½ + δ`, `0 < δ < δ₀`, has `|lam(n) − Λ(n)| < ε`. -/
theorem abs_sub_vonMangoldt_lt_of_isHerglotzProducerOn (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ lam : ℕ → ℝ,
      (∀ m, |lam m| ≤ Real.log m) → IsHerglotzProducerOn (1 / 2 + δ) lam →
        |lam n - ArithmeticFunction.vonMangoldt n| < ε := by
  by_contra hcon
  simp only [not_exists, not_and, not_forall, not_lt] at hcon
  have hpick : ∀ k : ℕ, ∃ lam : ℕ → ℝ, (∀ m, |lam m| ≤ Real.log m) ∧
      IsHerglotzProducerOn (1 / 2 + 1 / ((k : ℝ) + 2)) lam ∧
        ε ≤ |lam n - ArithmeticFunction.vonMangoldt n| := by
    intro k
    obtain ⟨δ, hδ, hδk, lam, hlam, hprod, hfar⟩ := hcon (1 / ((k : ℝ) + 2)) (by positivity)
    exact ⟨lam, hlam, hprod.mono (by linarith), hfar⟩
  choose lamk hlamk hprod hfar using hpick
  set K : Set (ℕ → ℝ) := univ.pi fun m => Icc (-Real.log m) (Real.log m) with hKdef
  have hK : IsCompact K := isCompact_univ_pi fun _ => isCompact_Icc
  have hmem : ∀ k, lamk k ∈ K := fun k => mem_univ_pi.mpr fun m => abs_le.mp (hlamk k m)
  obtain ⟨lam₀, hlam₀K, φ, hφ, hlim⟩ := hK.tendsto_subseq hmem
  have hlam₀ : ∀ m, |lam₀ m| ≤ Real.log m := fun m => abs_le.mpr (mem_univ_pi.mp hlam₀K m)
  have hlimn : ∀ m, Tendsto (fun k => lamk (φ k) m) atTop (𝓝 (lam₀ m)) :=
    fun m => (continuous_apply m).continuousAt.tendsto.comp hlim
  have hprodφ : ∀ k : ℕ, IsHerglotzProducerOn (1 / 2 + 1 / ((k : ℝ) + 2)) (lamk (φ k)) := by
    intro k
    refine (hprod (φ k)).mono ?_
    have h1 : (k : ℝ) ≤ φ k := by exact_mod_cast hφ.id_le k
    have : 1 / ((φ k : ℝ) + 2) ≤ 1 / ((k : ℝ) + 2) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    linarith
  obtain ⟨Φ, hΦd, hΦre, hΦ⟩ := isHerglotzProducerOn_of_tendsto (by norm_num) (by norm_num)
    (fun k m => hlamk (φ k) m) hprodφ hlimn
  have heq := (herglotzProducer_eq_vonMangoldt (fun σ hσ => summable_abs_div_rpow_of_log hlam₀ hσ)
    hΦd hΦre hΦ).2
  have hval : lam₀ n = ArithmeticFunction.vonMangoldt n := by
    rcases Nat.lt_or_ge n 2 with hn | hn
    · have hlog : Real.log n = 0 := by
        interval_cases n <;> simp
      have h0 := hlam₀ n
      rw [hlog, abs_nonpos_iff] at h0
      rw [h0]
      interval_cases n <;> simp
    · exact heq n hn
  have hlimabs : Tendsto (fun k => |lamk (φ k) n - ArithmeticFunction.vonMangoldt n|) atTop
      (𝓝 |lam₀ n - ArithmeticFunction.vonMangoldt n|) :=
    ((hlimn n).sub_const _).abs
  have hge : ε ≤ |lam₀ n - ArithmeticFunction.vonMangoldt n| :=
    ge_of_tendsto hlimabs (Eventually.of_forall fun k => hfar (φ k))
  rw [hval, sub_self, abs_zero] at hge
  linarith

end RHTower.RelaxedHerglotz
