import GaloisForLFunctions.RHTower.WeilLagFunctionDense

/-!
# Lag progressions decide RH on every non-meagre set of spacings

For a spacing `L` the progression `m ↦ Φ(mL)`, `m ∈ ℕ`, samples the lag function
`Φ(L) = Σ_ρ e^{L(ρ−½)}/(ρ(1−ρ))` on `Lℕ`.  One progression is not known to decide RH: when the
supremum of `Re ρ` is not attained, the off-line terms can in principle cancel along a single
progression.  A family of spacings does decide RH as soon as it is not meagre.

**Theorem** (`riemannHypothesis_iff_not_isMeagre_bddAbove_progression`).  RH holds iff the set of
spacings `L ∈ ℝ` for which `m ↦ Φ(mL)` is bounded above is not meagre.  Under RH that set is all
of `ℝ`; otherwise its complement, the spacings with `sup_m Φ(mL) = +∞`, is residual
(`residual_not_bddAbove_progression_of_not_riemannHypothesis`).

Proof.  The level sets `T_k = {L | ∀ m, Φ(mL) ≤ k}` are closed because `Φ` is continuous, they
are symmetric under `L ↦ −L` because `Φ` is even, and the bounded spacings form `⋃_k T_k`.  If
that union is not meagre then by Baire some `T_k` has an interior point, and by symmetry `T_k`
contains an interval `(c, d)` with `0 < c < d`.  Every `u > cd/(d − c)` is `m·(u/m)` with
`m = ⌊u/d⌋ + 1` and `u/m ∈ (c, d)`, so `Φ ≤ k` on a half-line, and the one-sided lag criterion
gives RH.
-/

open Set Topology Filter

namespace RHTower

noncomputable section

/-- The spacings `L` whose lag progression `Φ(mL)` stays below `k`. -/
def lagProgressionLevel (k : ℝ) : Set ℝ := {L | ∀ m : ℕ, weilLagFunctionReal (m * L) ≤ k}

theorem isClosed_lagProgressionLevel (k : ℝ) : IsClosed (lagProgressionLevel k) := by
  have h : lagProgressionLevel k = ⋂ m : ℕ, {L : ℝ | weilLagFunctionReal (m * L) ≤ k} := by
    ext L; simp [lagProgressionLevel]
  rw [h]
  exact isClosed_iInter fun m =>
    isClosed_le (continuous_weilLagFunctionReal.comp (continuous_const.mul continuous_id))
      continuous_const

theorem neg_mem_lagProgressionLevel {k L : ℝ} (h : L ∈ lagProgressionLevel k) :
    -L ∈ lagProgressionLevel k := fun m => by
  rw [mul_neg, weilLagFunctionReal_neg]; exact h m

/-- **Interval of spacings.**  A uniform bound on all progressions with spacing in an interval
`(c, d)`, `0 < c < d`, gives RH. -/
theorem riemannHypothesis_of_Ioo_subset_lagProgressionLevel {c d k : ℝ} (hc : 0 < c)
    (hcd : c < d) (h : Ioo c d ⊆ lagProgressionLevel k) : RiemannHypothesis := by
  have hd : 0 < d := hc.trans hcd
  have hdc : 0 < d - c := sub_pos.mpr hcd
  refine riemannHypothesis_of_bddAbove_on_dense
    (S := {u | ∃ m : ℕ, ∃ L ∈ Ioo c d, u = m * L}) (L₀ := c * d / (d - c) + d) (M := k)
    (fun u hu => subset_closure ?_) ?_
  · have hu' : c * d / (d - c) + d ≤ u := hu
    have hcd0 : 0 ≤ c * d / (d - c) := by positivity
    have hu0 : 0 < u := by linarith
    have hm1 := Nat.lt_floor_add_one (u / d)
    have hm2 := Nat.floor_le (div_pos hu0 hd).le
    set m : ℕ := ⌊u / d⌋₊ + 1 with hm
    have hmR : (m : ℝ) = (⌊u / d⌋₊ : ℝ) + 1 := by rw [hm]; push_cast; ring
    have hmpos : (0 : ℝ) < m := by rw [hmR]; positivity
    have hlow : u / d < m := by rw [hmR]; exact hm1
    have hupp : (m : ℝ) ≤ u / d + 1 := by rw [hmR]; linarith
    have hkey : c * (u / d + 1) < u := by
      have h1 : c * d / (d - c) < u := by linarith
      rw [div_lt_iff₀ hdc] at h1
      have : c * (u / d + 1) = (c * u + c * d) / d := by field_simp
      rw [this, div_lt_iff₀ hd]
      nlinarith
    refine ⟨m, u / m, ⟨?_, ?_⟩, by field_simp⟩
    · rw [lt_div_iff₀ hmpos]
      calc c * m ≤ c * (u / d + 1) := mul_le_mul_of_nonneg_left hupp hc.le
        _ < u := hkey
    · rw [div_lt_iff₀ hmpos]
      have := (div_lt_iff₀ hd).mp hlow
      linarith
  · rintro u ⟨m, L, hL, rfl⟩
    exact h hL m

/-- An interior point of a level set forces RH. -/
theorem riemannHypothesis_of_interior_lagProgressionLevel_nonempty {k : ℝ}
    (h : (interior (lagProgressionLevel k)).Nonempty) : RiemannHypothesis := by
  obtain ⟨L₀, hL₀⟩ := h
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hL₀)
  have habs : Metric.ball |L₀| ε ⊆ lagProgressionLevel k := by
    intro L hL
    rcases le_or_gt 0 L₀ with h0 | h0
    · rw [abs_of_nonneg h0] at hL; exact hball hL
    · rw [abs_of_neg h0] at hL
      have : -L ∈ Metric.ball L₀ ε := by
        rw [Metric.mem_ball, Real.dist_eq] at hL ⊢
        rw [show -L - L₀ = -(L - -L₀) by ring, abs_neg]; exact hL
      simpa using neg_mem_lagProgressionLevel (hball this)
  refine riemannHypothesis_of_Ioo_subset_lagProgressionLevel (c := |L₀| + ε / 2)
    (d := |L₀| + ε) (k := k) (by positivity) (by linarith) fun L hL => habs ?_
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  constructor <;> linarith [hL.1, hL.2]

theorem weilLagFunctionReal_le_poleSharpConstant (hRH : RiemannHypothesis) (L : ℝ) :
    weilLagFunctionReal L ≤ poleSharpConstant :=
  (Complex.re_le_norm _).trans (norm_weilLagFunction_le_of_riemannHypothesis hRH L)

/-- The bounded spacings are the union of the level sets. -/
theorem setOf_bddAbove_progression_subset :
    {L : ℝ | BddAbove (range fun m : ℕ => weilLagFunctionReal (m * L))} ⊆
      ⋃ k : ℕ, lagProgressionLevel k := by
  rintro L ⟨M, hM⟩
  refine mem_iUnion.mpr ⟨⌈M⌉₊, fun m => ?_⟩
  exact (hM ⟨m, rfl⟩).trans (Nat.le_ceil M)

/-- **Off RH the bounded spacings are meagre.** -/
theorem isMeagre_bddAbove_progression_of_not_riemannHypothesis (hRH : ¬ RiemannHypothesis) :
    IsMeagre {L : ℝ | BddAbove (range fun m : ℕ => weilLagFunctionReal (m * L))} := by
  refine IsMeagre.mono setOf_bddAbove_progression_subset (isMeagre_iUnion fun k => ?_)
  refine IsNowhereDense.isMeagre ((isClosed_lagProgressionLevel _).isNowhereDense_iff.mpr ?_)
  by_contra hne
  exact hRH (riemannHypothesis_of_interior_lagProgressionLevel_nonempty
    (Set.nonempty_iff_ne_empty.mpr hne))

/-- **Off RH, `sup_m Φ(mL) = +∞` for a residual set of spacings.** -/
theorem residual_not_bddAbove_progression_of_not_riemannHypothesis (hRH : ¬ RiemannHypothesis) :
    {L : ℝ | ¬ BddAbove (range fun m : ℕ => weilLagFunctionReal (m * L))} ∈ residual ℝ := by
  have := isMeagre_bddAbove_progression_of_not_riemannHypothesis hRH
  rw [IsMeagre] at this
  simpa [Set.compl_setOf] using this

/-- **RH ⟺ the spacings with bounded lag progression are not meagre.** -/
theorem riemannHypothesis_iff_not_isMeagre_bddAbove_progression :
    RiemannHypothesis ↔
      ¬ IsMeagre {L : ℝ | BddAbove (range fun m : ℕ => weilLagFunctionReal (m * L))} := by
  constructor
  · intro hRH
    have huniv : {L : ℝ | BddAbove (range fun m : ℕ => weilLagFunctionReal (m * L))} = univ := by
      ext L
      simp only [mem_setOf_eq, mem_univ, iff_true]
      exact ⟨poleSharpConstant, by
        rintro _ ⟨m, rfl⟩; exact weilLagFunctionReal_le_poleSharpConstant hRH _⟩
    rw [huniv]
    exact not_isMeagre_of_isOpen isOpen_univ univ_nonempty
  · intro h
    by_contra hRH
    exact h (isMeagre_bddAbove_progression_of_not_riemannHypothesis hRH)

/-- **Interval form.**  RH holds iff, for some nonempty open interval of spacings, every lag
progression with spacing in it is bounded above. -/
theorem riemannHypothesis_iff_exists_Ioo_bddAbove_progression :
    RiemannHypothesis ↔ ∃ a b : ℝ, a < b ∧
      ∀ L ∈ Ioo a b, BddAbove (range fun m : ℕ => weilLagFunctionReal (m * L)) := by
  constructor
  · intro hRH
    refine ⟨0, 1, one_pos, fun L _ => ⟨poleSharpConstant, ?_⟩⟩
    rintro _ ⟨m, rfl⟩; exact weilLagFunctionReal_le_poleSharpConstant hRH _
  · rintro ⟨a, b, hab, h⟩
    refine riemannHypothesis_iff_not_isMeagre_bddAbove_progression.mpr fun hmeagre => ?_
    exact not_isMeagre_of_isOpen isOpen_Ioo (nonempty_Ioo.mpr hab) (hmeagre.mono h)

end

end RHTower
