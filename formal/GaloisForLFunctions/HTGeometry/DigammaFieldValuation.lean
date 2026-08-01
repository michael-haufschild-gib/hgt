import GaloisForLFunctions.HTGeometry.PolygammaVerticalDecay
import GaloisForLFunctions.RHTower.DigammaImaginaryVerticalAsymptotic
import GaloisForLFunctions.HTGeometry.JetPolynomialDerivative

/-!
# The valuation of the digamma field on a vertical line

On a vertical line the digamma is `log t + iπ/2 + o(1)` and every higher polygamma vanishes.  So in a
jet polynomial of the digamma tower, a monomial contributes at logarithmic order equal to its degree
in `ψ`, and any monomial carrying a derivative factor is negligible.

Normalizing by the `D`-th power of the leading logarithm therefore isolates the coefficient of the
pure monomial `ψ^D`: this is eq. (19) of the projective-boundary law for the digamma field with
constant coefficients.
-/

open Filter Topology Complex

namespace GaloisForLFunctions

/-- The leading logarithm of the vertical digamma asymptotic. -/
noncomputable def vertLog (t : ℝ) : ℂ := (Real.log t : ℂ) + (Real.pi / 2 : ℂ) * Complex.I

theorem tendsto_norm_vertLog : Tendsto (fun t : ℝ => ‖vertLog t‖) atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ Real.tendsto_log_atTop
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
  have hre : (vertLog t).re = Real.log t := by simp [vertLog]
  calc Real.log t = |(vertLog t).re| := by
        rw [hre, abs_of_pos (Real.log_pos ht)]
    _ ≤ ‖vertLog t‖ := Complex.abs_re_le_norm _

theorem eventually_vertLog_ne_zero : ∀ᶠ t : ℝ in atTop, vertLog t ≠ 0 := by
  filter_upwards [tendsto_norm_vertLog.eventually_gt_atTop 0] with t ht
  intro h
  rw [h] at ht
  simp at ht

/-- The digamma on a vertical line, normalized by the leading logarithm, tends to one. -/
theorem tendsto_digamma_div_vertLog {σ : ℝ} (hσ : 0 ≤ σ) :
    Tendsto (fun t : ℝ => Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) / vertLog t)
      atTop (nhds 1) := by
  have hsub : Tendsto (fun t : ℝ =>
      Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) - vertLog t) atTop (nhds 0) :=
    RHTower.digamma_vertical_sub_log_I_tendsto_zero σ hσ
  have hinv : Tendsto (fun t : ℝ => ‖vertLog t‖⁻¹) atTop (nhds 0) :=
    tendsto_norm_vertLog.inv_tendsto_atTop
  have hquot : Tendsto (fun t : ℝ =>
      (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) - vertLog t) / vertLog t)
      atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hb : Tendsto (fun t : ℝ =>
        ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) - vertLog t‖ * ‖vertLog t‖⁻¹)
        atTop (nhds 0) := by
      have hn : Tendsto (fun t : ℝ =>
          ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) - vertLog t‖) atTop (nhds 0) := by
        rw [← tendsto_zero_iff_norm_tendsto_zero] at *
        exact hsub
      simpa using hn.mul hinv
    refine hb.congr fun t => ?_
    rw [norm_div, div_eq_mul_inv]
  have hone : Tendsto (fun t : ℝ =>
      1 + (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) - vertLog t) / vertLog t)
      atTop (nhds 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℂ)) (f := atTop (α := ℝ))).add hquot
  refine hone.congr' ?_
  filter_upwards [eventually_vertLog_ne_zero] with t ht
  field_simp
  ring

variable {σ : ℝ} {n N : ℕ}

/-- The jets of digamma along a vertical line. -/
noncomputable def digammaJetLine (σ : ℝ) (j : ℕ) (t : ℝ) : ℂ :=
  iteratedDeriv j Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)

/-- The derivative factors of a jet monomial vanish along a vertical line. -/
theorem tendsto_tail_prod (hσ : 0 < σ) (ex : Fin (n + 1) → ℕ) :
    Tendsto (fun t : ℝ => ∏ j : Fin n, (digammaJetLine σ ((j.succ : Fin (n + 1)) : ℕ) t) ^ (ex j.succ))
      atTop (nhds (∏ j : Fin n, (0 : ℂ) ^ (ex j.succ))) := by
  refine tendsto_finsetProd _ fun j _ => ?_
  have hval : ((j.succ : Fin (n + 1)) : ℕ) = (j : ℕ) + 1 := by simp
  have hbase : Tendsto (fun t : ℝ => digammaJetLine σ ((j.succ : Fin (n + 1)) : ℕ) t)
      atTop (nhds 0) := by
    simp only [digammaJetLine, hval]
    exact tendsto_iteratedDeriv_succ_digamma_vertical hσ (j : ℕ)
  exact hbase.pow _

theorem tendsto_one_div_vertLog_pow {k : ℕ} (hk : 0 < k) :
    Tendsto (fun t : ℝ => 1 / (vertLog t) ^ k) atTop (nhds 0) := by
  have hnorm : Tendsto (fun t : ℝ => ‖vertLog t‖ ^ k) atTop atTop :=
    (tendsto_pow_atTop hk.ne').comp tendsto_norm_vertLog
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine hnorm.inv_tendsto_atTop.congr fun t => ?_
  simp [norm_pow]

theorem tendsto_head_div (hσ : 0 ≤ σ) (k D : ℕ) (hkD : k ≤ D) :
    Tendsto (fun t : ℝ => (digammaJetLine σ 0 t) ^ k / (vertLog t) ^ D) atTop
      (nhds (if k = D then 1 else 0)) := by
  have hbase : Tendsto (fun t : ℝ => digammaJetLine σ 0 t / vertLog t) atTop (nhds 1) := by
    have := tendsto_digamma_div_vertLog hσ
    refine this.congr fun t => ?_
    rw [digammaJetLine, iteratedDeriv_zero]
  by_cases hk : k = D
  · subst hk
    rw [if_pos rfl]
    have hp := hbase.pow k
    rw [one_pow] at hp
    refine hp.congr' ?_
    filter_upwards [eventually_vertLog_ne_zero] with t ht
    rw [div_pow]
  · rw [if_neg hk]
    have hlt : k < D := lt_of_le_of_ne hkD hk
    obtain ⟨m, hm⟩ : ∃ m : ℕ, D = k + m := ⟨D - k, by omega⟩
    have hmpos : 0 < m := by omega
    have hprod := (hbase.pow k).mul (tendsto_one_div_vertLog_pow hmpos)
    rw [one_pow, one_mul] at hprod
    refine hprod.congr' ?_
    filter_upwards [eventually_vertLog_ne_zero] with t ht
    rw [div_pow, hm, pow_add, div_mul_div_comm, mul_one]

/-- A jet monomial normalized by `L^D` converges: to the tail limit when its digamma degree is `D`,
and to zero when it is smaller. -/
theorem tendsto_monomial_div (hσ : 0 < σ) (ex : Fin (n + 1) → ℕ) (D : ℕ) (hle : ex 0 ≤ D) :
    Tendsto (fun t : ℝ =>
      (∏ j : Fin (n + 1), (digammaJetLine σ (j : ℕ) t) ^ (ex j)) / (vertLog t) ^ D) atTop
      (nhds ((if ex 0 = D then (1 : ℂ) else 0) * ∏ j : Fin n, (0 : ℂ) ^ (ex j.succ))) := by
  have hsplit : ∀ t : ℝ, (∏ j : Fin (n + 1), (digammaJetLine σ (j : ℕ) t) ^ (ex j)) / (vertLog t) ^ D
      = ((digammaJetLine σ 0 t) ^ (ex 0) / (vertLog t) ^ D) *
        ∏ j : Fin n, (digammaJetLine σ ((j.succ : Fin (n + 1)) : ℕ) t) ^ (ex j.succ) := by
    intro t
    rw [Fin.prod_univ_succ]
    ring_nf
    rw [Fin.val_zero]
    ring
  have hlim := (tendsto_head_div (le_of_lt hσ) (ex 0) D hle).mul (tendsto_tail_prod hσ ex)
  exact hlim.congr fun t => (hsplit t).symm

/-- **Eq. (19) for the digamma field with constant coefficients.**  A jet polynomial in the digamma
tower, normalized by the `D`-th power of the vertical logarithm, converges to the coefficient of the
pure monomial `ψ^D`: every monomial carrying a derivative factor vanishes, and every monomial of
lower degree in `ψ` is of lower logarithmic order. -/
theorem tendsto_jetPoly_digamma_div (hσ : 0 < σ) (d : Fin N → ℂ) (e : Fin N → Fin (n + 1) → ℕ)
    (D : ℕ) (β : Fin N) (hβpure : ∀ j : Fin n, e β j.succ = 0) (hβdeg : e β 0 = D)
    (hle : ∀ α, e α 0 ≤ D)
    (hother : ∀ α, α ≠ β → e α 0 < D ∨ ∃ j : Fin n, e α j.succ ≠ 0) :
    Tendsto (fun t : ℝ =>
      jetPoly d e (fun j : Fin (n + 1) => digammaJetLine σ (j : ℕ) t) / (vertLog t) ^ D)
      atTop (nhds (d β)) := by
  classical
  have hval : ∀ α : Fin N,
      d α * ((if e α 0 = D then (1 : ℂ) else 0) * ∏ j : Fin n, (0 : ℂ) ^ (e α j.succ))
        = if α = β then d β else 0 := by
    intro α
    by_cases hαβ : α = β
    · subst hαβ
      have htail : ∏ j : Fin n, (0 : ℂ) ^ (e α j.succ) = 1 := by
        refine Finset.prod_eq_one fun j _ => ?_
        rw [hβpure j, pow_zero]
      rw [if_pos rfl, htail, if_pos hβdeg, mul_one, mul_one]
    · rw [if_neg hαβ]
      rcases hother α hαβ with hlt | ⟨j, hj⟩
      · rw [if_neg (Nat.ne_of_lt hlt), zero_mul, mul_zero]
      · have htail : ∏ i : Fin n, (0 : ℂ) ^ (e α i.succ) = 0 := by
          refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
          exact zero_pow hj
        rw [htail, mul_zero, mul_zero]
  have hterm : ∀ α : Fin N, Tendsto (fun t : ℝ =>
      d α * ((∏ j : Fin (n + 1), (digammaJetLine σ (j : ℕ) t) ^ (e α j)) / (vertLog t) ^ D))
      atTop (nhds (if α = β then d β else 0)) := by
    intro α
    have := (tendsto_monomial_div hσ (e α) D (hle α)).const_mul (d α)
    rw [hval α] at this
    exact this
  have hsum : Tendsto (fun t : ℝ =>
      ∑ α : Fin N, d α * ((∏ j : Fin (n + 1), (digammaJetLine σ (j : ℕ) t) ^ (e α j))
        / (vertLog t) ^ D)) atTop (nhds (∑ α : Fin N, if α = β then d β else 0)) :=
    tendsto_finsetSum _ fun α _ => hterm α
  rw [Finset.sum_ite_eq' Finset.univ β (fun _ => d β)] at hsum
  simp only [Finset.mem_univ, if_pos] at hsum
  refine hsum.congr fun t => ?_
  rw [jetPoly, Finset.sum_div]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [mul_div_assoc]

end GaloisForLFunctions
