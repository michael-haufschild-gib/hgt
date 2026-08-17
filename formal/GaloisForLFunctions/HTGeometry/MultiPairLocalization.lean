import GaloisForLFunctions.HTGeometry.LogConcaveSeparation

/-!
# Localization for several conjugate pairs

The reduction that made the one-pair criterion finite survives any number of pairs.  A sum of `r`
modulated cosines whose real parts lie in `[b₋, b₊]` never exceeds `2r (e^{b₋ t} + e^{b₊ t})`, an
explicit two-term positive exponential sum.  Wherever the compared sum `R` clears that envelope the
comparison is automatic, and the set where it does not is bounded as soon as some exponent of `R`
lies strictly below `b₋` and some strictly above `b₊`.

So the comparison over the whole line reduces to one explicit compact interval, for arbitrarily many
pairs.  What does *not* survive is the certificate: see `ExponentialCertificateGap` for the chord
obstruction and `LogConcaveSeparation` for what replaces the single profile.
-/

open Set Real

namespace GaloisForLFunctions.HTGeometry

variable {m r : ℕ}

private theorem lt_log_of_exp_lt {p K : ℝ} (h : Real.exp p < K) : p < Real.log K := by
  have := Real.log_lt_log (Real.exp_pos p) h
  rwa [Real.log_exp] at this

/-- Every exponential with rate in `[b₋, b₊]` is below the two-term envelope. -/
theorem exp_mul_le_envelope {bmin bmax b t : ℝ} (h1 : bmin ≤ b) (h2 : b ≤ bmax) :
    Real.exp (b * t) ≤ Real.exp (bmin * t) + Real.exp (bmax * t) := by
  rcases le_total 0 t with ht | ht
  · have hle : Real.exp (b * t) ≤ Real.exp (bmax * t) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right h2 ht)
    linarith [Real.exp_pos (bmin * t)]
  · have hle : Real.exp (b * t) ≤ Real.exp (bmin * t) :=
      Real.exp_le_exp.mpr (by nlinarith)
    linarith [Real.exp_pos (bmax * t)]

/-- **The envelope bound.**  A sum of `r` modulated cosines with real parts in `[b₋, b₊]` is bounded
by `2r (e^{b₋ t} + e^{b₊ t})` at every point. -/
theorem multiPair_le_envelope (β γ δ : Fin r → ℝ) {bmin bmax : ℝ}
    (hbmin : ∀ k, bmin ≤ β k) (hbmax : ∀ k, β k ≤ bmax) (t : ℝ) :
    ∑ k, 2 * Real.exp (β k * t) * Real.cos (γ k * t + δ k)
      ≤ 2 * r * (Real.exp (bmin * t) + Real.exp (bmax * t)) := by
  have hterm : ∀ k : Fin r, 2 * Real.exp (β k * t) * Real.cos (γ k * t + δ k)
      ≤ 2 * (Real.exp (bmin * t) + Real.exp (bmax * t)) := by
    intro k
    have hcos : Real.cos (γ k * t + δ k) ≤ 1 := Real.cos_le_one _
    have hpos : (0 : ℝ) < Real.exp (β k * t) := Real.exp_pos _
    have henv := exp_mul_le_envelope (hbmin k) (hbmax k) (t := t)
    nlinarith
  calc ∑ k, 2 * Real.exp (β k * t) * Real.cos (γ k * t + δ k)
      ≤ ∑ _k : Fin r, 2 * (Real.exp (bmin * t) + Real.exp (bmax * t)) :=
        Finset.sum_le_sum (fun k _ => hterm k)
    _ = 2 * r * (Real.exp (bmin * t) + Real.exp (bmax * t)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- **Boundedness of the exceptional set.**  If some exponent of `R` lies strictly below `b₋` and
some strictly above `b₊`, the set where `R` fails to clear the envelope is bounded, with an explicit
bound built from the two straddling exponents. -/
theorem envelope_exceptional_bounded (c a : Fin m → ℝ) (hc : ∀ i, 0 < c i)
    {bmin bmax D : ℝ} (hD : 0 < D) (hb : bmin ≤ bmax) {i j : Fin m}
    (hi : a i < bmin) (hj : bmax < a j) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ,
      expSum c a t < D * (Real.exp (bmin * t) + Real.exp (bmax * t)) → |t| ≤ T := by
  set Li : ℝ := Real.log (2 * D / c i) / (a i - bmin) with hLi
  set Uj : ℝ := Real.log (2 * D / c j) / (a j - bmax) with hUj
  refine ⟨max |Li| |Uj|, le_trans (abs_nonneg _) (le_max_left _ _), ?_⟩
  intro t ht
  have hterm : ∀ k : Fin m, c k * Real.exp (a k * t) ≤ expSum c a t := by
    intro k
    rw [expSum]
    exact Finset.single_le_sum (f := fun k => c k * Real.exp (a k * t))
      (fun k _ => (mul_pos (hc k) (Real.exp_pos _)).le) (Finset.mem_univ k)
  have hdi : a i - bmin < 0 := by linarith
  have hdj : (0 : ℝ) < a j - bmax := by linarith
  rcases le_total 0 t with htsign | htsign
  · -- to the right the upper branch dominates the envelope
    have hbb : Real.exp (bmin * t) ≤ Real.exp (bmax * t) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hb htsign)
    have hstep : c j * Real.exp (a j * t) < 2 * D * Real.exp (bmax * t) := by
      have := lt_of_le_of_lt (hterm j) ht
      nlinarith [Real.exp_pos (bmin * t)]
    have h1 : Real.exp ((a j - bmax) * t) < 2 * D / c j := by
      rw [show (a j - bmax) * t = a j * t - bmax * t from by ring, Real.exp_sub,
        div_lt_iff₀ (Real.exp_pos _), div_mul_eq_mul_div, lt_div_iff₀ (hc j)]
      nlinarith [hstep]
    have h2 : (a j - bmax) * t < Real.log (2 * D / c j) := lt_log_of_exp_lt h1
    have h3 : t < Uj := by rw [hUj, lt_div_iff₀ hdj]; linarith
    refine abs_le.mpr ⟨?_, ?_⟩
    · have : (0 : ℝ) ≤ max |Li| |Uj| := le_trans (abs_nonneg _) (le_max_left _ _)
      linarith
    · have h4 : Uj ≤ |Uj| := le_abs_self Uj
      have h5 : |Uj| ≤ max |Li| |Uj| := le_max_right _ _
      linarith
  · -- to the left the lower branch dominates
    have hbb : Real.exp (bmax * t) ≤ Real.exp (bmin * t) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hstep : c i * Real.exp (a i * t) < 2 * D * Real.exp (bmin * t) := by
      have := lt_of_le_of_lt (hterm i) ht
      nlinarith [Real.exp_pos (bmax * t)]
    have h1 : Real.exp ((a i - bmin) * t) < 2 * D / c i := by
      rw [show (a i - bmin) * t = a i * t - bmin * t from by ring, Real.exp_sub,
        div_lt_iff₀ (Real.exp_pos _), div_mul_eq_mul_div, lt_div_iff₀ (hc i)]
      nlinarith [hstep]
    have h2 : (a i - bmin) * t < Real.log (2 * D / c i) := lt_log_of_exp_lt h1
    have h3 : Li < t := by rw [hLi, div_lt_iff_of_neg hdi]; linarith
    refine abs_le.mpr ⟨?_, ?_⟩
    · have h4 : -|Li| ≤ Li := neg_abs_le Li
      have h5 : -(max |Li| |Uj|) ≤ -|Li| := by simp
      linarith
    · have : (0 : ℝ) ≤ max |Li| |Uj| := le_trans (abs_nonneg _) (le_max_left _ _)
      linarith

/-- **Multi-pair localization.**  Under strict straddling, the comparison of a positive exponential
sum with any finite family of modulated cosines reduces to one explicit compact interval. -/
theorem multiPair_le_iff_on_Icc (c a : Fin m → ℝ) (hc : ∀ i, 0 < c i)
    (β γ δ : Fin r → ℝ) {bmin bmax : ℝ} (hr : 0 < r) (hb : bmin ≤ bmax)
    (hbmin : ∀ k, bmin ≤ β k) (hbmax : ∀ k, β k ≤ bmax) {i j : Fin m}
    (hi : a i < bmin) (hj : bmax < a j) :
    ∃ T : ℝ, 0 ≤ T ∧
      ((∀ t : ℝ, ∑ k, 2 * Real.exp (β k * t) * Real.cos (γ k * t + δ k) ≤ expSum c a t)
        ↔ ∀ t ∈ Icc (-T) T,
            ∑ k, 2 * Real.exp (β k * t) * Real.cos (γ k * t + δ k) ≤ expSum c a t) := by
  have hDpos : (0 : ℝ) < 2 * r := by
    have : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
    linarith
  obtain ⟨T, hT0, hT⟩ := envelope_exceptional_bounded c a hc hDpos hb hi hj
  refine ⟨T, hT0, ⟨fun h t _ => h t, fun h t => ?_⟩⟩
  by_cases hmem : t ∈ Icc (-T) T
  · exact h t hmem
  · have hclear : 2 * r * (Real.exp (bmin * t) + Real.exp (bmax * t)) ≤ expSum c a t := by
      by_contra hcon
      push Not at hcon
      exact hmem (abs_le.mp (hT t hcon))
    exact le_trans (multiPair_le_envelope β γ δ hbmin hbmax t) hclear

end GaloisForLFunctions.HTGeometry
