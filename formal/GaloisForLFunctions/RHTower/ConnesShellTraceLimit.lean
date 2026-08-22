import GaloisForLFunctions.RHTower.ConnesShellReindex

/-!
# §V (31)–(33) at a non-archimedean place: the limit

§V (31)-(33) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

After (30) the trace is `∑_k (2N+1−|k|) w(k)` over the window `|k| ≤ 2N`, where `w` is the shell
profile of `ĝ` and `2N+1−|k|` is the discrete `2 log' Λ − log|u|` of batch 36.  The limit `Λ → ∞`
is `N → ∞`, and the assertion is that the windowed sum agrees, up to `o(1)`, with

  `(2N+1) ∑_k w(k) − ∑_k |k| w(k)`,

the two terms being Connes' `2h(1) log' Λ` and the principal value.

The proof does not estimate the two terms separately — that would need the tail of `∑ w` to be
`o(1/N)`.  Instead the difference is recognised as a *tail of the single convergent series*
`∑ |k| ‖w(k)‖`: off the window one has `|2N+1−|k|| = |k|−2N−1 ≤ |k|`, so the discarded mass is
dominated termwise by that series, and tails of a convergent series vanish.
-/

open Filter Topology

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- The symmetric integer windows exhaust `ℤ`. -/
theorem connes_intervalFinset_tendsto :
    Tendsto (fun M : ℕ => Finset.Icc (-(M : ℤ)) (M : ℤ)) atTop atTop := by
  refine tendsto_atTop_finset_of_monotone ?_ ?_
  · intro a b hab
    have hb : (a : ℤ) ≤ (b : ℤ) := by exact_mod_cast hab
    exact Finset.Icc_subset_Icc (by linarith) hb
  · intro k
    refine ⟨k.natAbs, ?_⟩
    rw [Finset.mem_Icc]
    omega

/-- The doubled symmetric windows exhaust `ℤ`. -/
theorem connes_doubleWindow_tendsto :
    Tendsto (fun N : ℕ => Finset.Icc (-(2 * (N : ℤ))) (2 * (N : ℤ))) atTop atTop := by
  have h := connes_intervalFinset_tendsto.comp (tendsto_id.const_mul_atTop' (by norm_num : 0 < 2))
  refine h.congr fun N => ?_
  show Finset.Icc (-((2 * N : ℕ) : ℤ)) ((2 * N : ℕ) : ℤ)
    = Finset.Icc (-(2 * (N : ℤ))) (2 * (N : ℤ))
  push_cast
  rfl

/-- **§V (31)–(33) at a non-archimedean place.**  The windowed trace sum agrees with the two main
terms up to `o(1)`. -/
theorem connes_shell_trace_expansion {w : ℤ → ℂ}
    (hw : Summable w) (hkw : Summable fun k : ℤ => (|k| : ℝ) * ‖w k‖) :
    Tendsto (fun N : ℕ =>
        (∑ k ∈ Finset.Icc (-(2 * (N : ℤ))) (2 * (N : ℤ)),
            ((2 * (N : ℤ) + 1 - |k| : ℤ) : ℂ) * w k)
          - ∑' k : ℤ, ((2 * (N : ℤ) + 1 - |k| : ℤ) : ℂ) * w k)
      atTop (𝓝 0) := by
  have hcsum : ∀ N : ℕ, Summable fun k : ℤ => ((2 * (N : ℤ) + 1 - |k| : ℤ) : ℂ) * w k := by
    intro N
    have hA : Summable fun k : ℤ => ((2 * (N : ℤ) + 1 : ℤ) : ℂ) * w k := hw.mul_left _
    have hB : Summable fun k : ℤ => ((|k| : ℤ) : ℂ) * w k := by
      refine Summable.of_norm ?_
      refine hkw.congr fun k => ?_
      rw [norm_mul]
      congr 1
      rw [Complex.norm_intCast, Int.cast_abs]
      simp
    refine (hA.sub hB).congr fun k => ?_
    push_cast
    ring
  have hbound : ∀ N : ℕ,
      ‖(∑ k ∈ Finset.Icc (-(2 * (N : ℤ))) (2 * (N : ℤ)),
            ((2 * (N : ℤ) + 1 - |k| : ℤ) : ℂ) * w k)
          - ∑' k : ℤ, ((2 * (N : ℤ) + 1 - |k| : ℤ) : ℂ) * w k‖
        ≤ ∑' k : ↥((↑(Finset.Icc (-(2 * (N : ℤ))) (2 * (N : ℤ))) : Set ℤ)ᶜ),
            (|(k : ℤ)| : ℝ) * ‖w (k : ℤ)‖ := by
    intro N
    have hsplit := (hcsum N).sum_add_tsum_compl
      (s := Finset.Icc (-(2 * (N : ℤ))) (2 * (N : ℤ)))
    have hrw : (∑ k ∈ Finset.Icc (-(2 * (N : ℤ))) (2 * (N : ℤ)),
          ((2 * (N : ℤ) + 1 - |k| : ℤ) : ℂ) * w k)
        - ∑' k : ℤ, ((2 * (N : ℤ) + 1 - |k| : ℤ) : ℂ) * w k
        = -∑' k : ↥((↑(Finset.Icc (-(2 * (N : ℤ))) (2 * (N : ℤ))) : Set ℤ)ᶜ),
            ((2 * (N : ℤ) + 1 - |(k : ℤ)| : ℤ) : ℂ) * w (k : ℤ) := by
      rw [← hsplit]
      ring
    rw [hrw, norm_neg]
    have htail : Summable fun k : ↥((↑(Finset.Icc (-(2 * (N : ℤ))) (2 * (N : ℤ))) : Set ℤ)ᶜ) =>
        ((2 * (N : ℤ) + 1 - |(k : ℤ)| : ℤ) : ℂ) * w (k : ℤ) :=
      ((hcsum N).subtype _)
    refine le_trans (norm_tsum_le_tsum_norm (htail.norm)) ?_
    refine Summable.tsum_le_tsum (fun k => ?_) htail.norm (hkw.subtype _)
    have hN : (0 : ℤ) ≤ (N : ℤ) := Int.natCast_nonneg N
    have hk : (2 * (N : ℤ)) < |(k : ℤ)| := by
      have h := k.2
      simp only [Finset.coe_Icc, Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at h
      rcases abs_cases ((k : ℤ)) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;> omega
    rw [norm_mul]
    have hc : ‖((2 * (N : ℤ) + 1 - |(k : ℤ)| : ℤ) : ℂ)‖ ≤ (|(k : ℤ)| : ℝ) := by
      rw [Complex.norm_intCast]
      have hnp : 2 * (N : ℤ) + 1 - |(k : ℤ)| ≤ 0 := by omega
      have hb : abs (2 * (N : ℤ) + 1 - |(k : ℤ)|) ≤ |(k : ℤ)| := by
        rw [abs_of_nonpos hnp]
        omega
      exact_mod_cast hb
    exact mul_le_mul_of_nonneg_right hc (norm_nonneg _)
  have hlim : Tendsto (fun N : ℕ =>
      ∑' k : ↥((↑(Finset.Icc (-(2 * (N : ℤ))) (2 * (N : ℤ))) : Set ℤ)ᶜ),
        (|(k : ℤ)| : ℝ) * ‖w (k : ℤ)‖) atTop (𝓝 0) :=
    (tendsto_tsum_compl_atTop_zero (fun k : ℤ => (|k| : ℝ) * ‖w k‖)).comp
      connes_doubleWindow_tendsto
  refine squeeze_zero_norm (fun N => hbound N) hlim

end

end GaloisForLFunctions.RHTower
