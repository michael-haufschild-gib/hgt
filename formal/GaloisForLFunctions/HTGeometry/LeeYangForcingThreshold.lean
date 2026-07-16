import GaloisForLFunctions.Core

/-!
# Forcing families on an interaction line: threshold trichotomy and marginal degeneracy

A *forcing family* is a set `L ⊆ ℝ` of interaction strengths at which a localization
property (real-rootedness of a partition function, positivity of a quadratic pencil,
Herglotz-ness of a carrier) holds, subject to Lee–Yang monotonicity: localization,
once achieved, persists under stronger interaction.  Formally `L` is an up-set.

The threshold `sInf L` splits the line into three strata, and the monotone mechanism
decides exactly two of them:

* `IsForcingFamily.mem_of_threshold_lt` — strictly above the threshold, membership is
  **forced**;
* `notMem_of_lt_threshold` — strictly below it, membership is **rejected**: the sign
  of the margin `t - sInf L` rejects the wrong-sign region outright;
* `IsForcingFamily.mem_iff_threshold_lt` — off the threshold, membership is a
  function of the margin sign alone.

At the threshold the mechanism degenerates:

* `threshold_membership_undetermined` — two forcing families share the same threshold
  and disagree at it (`Set.Ici 0` vs `Set.Ioi 0`), so no rule reading only the
  threshold value decides the marginal point (`no_threshold_decision_rule`);
* `closed_forcing_data_not_decide_marginal` — even adding closedness and the free
  half `0 ≤ sInf L`, the data does not pin the threshold to the physical point:
  `Set.Ici 0` and `Set.Ici 1` carry identical structure and disagree at `0`.

For a *closed* family the boundary bit is free (`csInf_mem_of_isClosed`), so the
membership question at a physical point `t₀` on the free side `t₀ ≤ sInf L` collapses
to an exact equality of reals (`mem_iff_eq_csInf_of_le`): localization at `t₀` is
precisely "the threshold is pinned at `t₀`" — a no-margin equality, not a margin
inequality.

An orientation-preserving affine change of the interaction coordinate transports the
family, the threshold, and marginality (`isForcingFamily_image_affine`,
`csInf_image_affine`, `marginal_transport`), so the threshold picture is independent
of the chosen presentation of the axis.
-/

open Set

namespace GaloisForLFunctions

/-- A **forcing family** of interaction strengths: localization, once achieved,
persists under increasing interaction — the set is an up-set in `ℝ`. -/
def IsForcingFamily (L : Set ℝ) : Prop :=
  ∀ ⦃s t : ℝ⦄, s ∈ L → s ≤ t → t ∈ L

/-- Closed rays are forcing families. -/
theorem isForcingFamily_Ici (a : ℝ) : IsForcingFamily (Ici a) :=
  fun _ _ hs hst => le_trans hs hst

/-- Open rays are forcing families. -/
theorem isForcingFamily_Ioi (a : ℝ) : IsForcingFamily (Ioi a) :=
  fun _ _ hs hst => lt_of_lt_of_le hs hst

/-- **Forced stratum.** Strictly above the threshold, membership is forced by the
monotone mechanism. -/
theorem IsForcingFamily.mem_of_threshold_lt {L : Set ℝ} (hL : IsForcingFamily L)
    (hne : L.Nonempty) (hbd : BddBelow L) {t : ℝ} (ht : sInf L < t) : t ∈ L := by
  obtain ⟨s, hsL, hst⟩ := (csInf_lt_iff hbd hne).mp ht
  exact hL hsL hst.le

/-- **Rejected stratum.** Strictly below the threshold, membership fails: the sign of
the margin `t - sInf L` rejects the wrong-sign region outright. -/
theorem notMem_of_lt_threshold {L : Set ℝ} (hbd : BddBelow L) {t : ℝ}
    (ht : t < sInf L) : t ∉ L :=
  fun hm => absurd (csInf_le hbd hm) (not_le.mpr ht)

/-- **The mechanism decides everything except the margin.** Off the threshold,
membership is a function of the margin sign alone. -/
theorem IsForcingFamily.mem_iff_threshold_lt {L : Set ℝ} (hL : IsForcingFamily L)
    (hne : L.Nonempty) (hbd : BddBelow L) {t : ℝ} (ht : t ≠ sInf L) :
    t ∈ L ↔ sInf L < t := by
  constructor
  · intro hm
    exact lt_of_le_of_ne (csInf_le hbd hm) (Ne.symm ht)
  · exact hL.mem_of_threshold_lt hne hbd

/-- A closed locus attains its threshold: for closed families the boundary bit is
free. -/
theorem csInf_mem_of_isClosed {L : Set ℝ} (hcl : IsClosed L) (hne : L.Nonempty)
    (hbd : BddBelow L) : sInf L ∈ L :=
  hcl.csInf_mem hne hbd

/-- **The no-margin equivalence.** For a closed locus and a physical point on the free
side `t₀ ≤ sInf L`, localization at the physical point is *exactly* the statement that
the threshold is pinned there: membership degenerates to an equality of reals, not a
margin inequality. -/
theorem mem_iff_eq_csInf_of_le {L : Set ℝ} (hcl : IsClosed L) (hne : L.Nonempty)
    (hbd : BddBelow L) {t₀ : ℝ} (hfree : t₀ ≤ sInf L) : t₀ ∈ L ↔ t₀ = sInf L := by
  constructor
  · intro hm
    exact le_antisymm hfree (csInf_le hbd hm)
  · rintro rfl
    exact hcl.csInf_mem hne hbd

/-- **Marginal degeneracy, bare form.** Two forcing families share their threshold and
disagree at it: the threshold value does not determine the boundary bit. -/
theorem threshold_membership_undetermined :
    ∃ L₁ L₂ : Set ℝ, IsForcingFamily L₁ ∧ IsForcingFamily L₂ ∧
      sInf L₁ = sInf L₂ ∧ sInf L₁ ∈ L₁ ∧ sInf L₂ ∉ L₂ := by
  refine ⟨Ici 0, Ioi 0, isForcingFamily_Ici 0, isForcingFamily_Ioi 0, ?_, ?_, ?_⟩
  · rw [csInf_Ici, csInf_Ioi]
  · rw [csInf_Ici]
    exact self_mem_Ici
  · rw [csInf_Ioi]
    exact fun h => lt_irrefl 0 (mem_Ioi.mp h)

/-- **No decision rule at the margin.** No predicate reading only the threshold value
decides membership at the threshold, uniformly across forcing families. -/
theorem no_threshold_decision_rule (d : ℝ → Prop) :
    ¬ ∀ L : Set ℝ, IsForcingFamily L → L.Nonempty → BddBelow L →
        (sInf L ∈ L ↔ d (sInf L)) := by
  intro h
  have h₁ := h (Ici 0) (isForcingFamily_Ici 0) nonempty_Ici bddBelow_Ici
  have h₂ := h (Ioi 0) (isForcingFamily_Ioi 0) nonempty_Ioi bddBelow_Ioi
  rw [csInf_Ici] at h₁
  rw [csInf_Ioi] at h₂
  exact lt_irrefl 0 (mem_Ioi.mp (h₂.mpr (h₁.mp self_mem_Ici)))

/-- **Why the marginal point is hard.** Even with closedness and the free half
`0 ≤ sInf L`, the mechanism's data does not determine localization at the physical
point `0`: two witnesses carry identical structure and disagree at `0`.  Deciding the
marginal point is equivalent to pinning the threshold — an input the forcing data does
not contain. -/
theorem closed_forcing_data_not_decide_marginal :
    ∃ L₁ L₂ : Set ℝ,
      (IsForcingFamily L₁ ∧ IsClosed L₁ ∧ L₁.Nonempty ∧ BddBelow L₁ ∧ 0 ≤ sInf L₁) ∧
      (IsForcingFamily L₂ ∧ IsClosed L₂ ∧ L₂.Nonempty ∧ BddBelow L₂ ∧ 0 ≤ sInf L₂) ∧
      (0 : ℝ) ∈ L₁ ∧ (0 : ℝ) ∉ L₂ := by
  refine ⟨Ici 0, Ici 1,
    ⟨isForcingFamily_Ici 0, isClosed_Ici, nonempty_Ici, bddBelow_Ici, ?_⟩,
    ⟨isForcingFamily_Ici 1, isClosed_Ici, nonempty_Ici, bddBelow_Ici, ?_⟩,
    self_mem_Ici, ?_⟩
  · rw [csInf_Ici]
  · rw [csInf_Ici]
    norm_num
  · rw [mem_Ici]
    norm_num

/-- An orientation-preserving affine reparametrization of the interaction axis carries
forcing families to forcing families. -/
theorem isForcingFamily_image_affine {L : Set ℝ} (hL : IsForcingFamily L) {a : ℝ}
    (ha : 0 < a) (b : ℝ) : IsForcingFamily ((fun x => a * x + b) '' L) := by
  rintro s t ⟨x, hxL, rfl⟩ hst
  have hy : x ≤ (t - b) / a := by
    rw [le_div_iff₀ ha]
    nlinarith
  refine ⟨(t - b) / a, hL hxL hy, ?_⟩
  field_simp
  ring

/-- The threshold transports through an orientation-preserving affine
reparametrization of the interaction axis. -/
theorem csInf_image_affine {L : Set ℝ} (hne : L.Nonempty) (hbd : BddBelow L) {a : ℝ}
    (ha : 0 < a) (b : ℝ) :
    sInf ((fun x => a * x + b) '' L) = a * sInf L + b := by
  refine IsGLB.csInf_eq ⟨?_, ?_⟩ (hne.image _)
  · rintro y ⟨x, hxL, rfl⟩
    have h1 : a * sInf L ≤ a * x := mul_le_mul_of_nonneg_left (csInf_le hbd hxL) ha.le
    linarith
  · intro c hc
    have hlb : ∀ x ∈ L, (c - b) / a ≤ x := by
      intro x hxL
      have hcx := hc ⟨x, hxL, rfl⟩
      rw [div_le_iff₀ ha]
      nlinarith
    have hs := le_csInf hne hlb
    rw [div_le_iff₀ ha] at hs
    nlinarith

/-- **Marginality is presentation-independent**: the physical point is the threshold
in one affine presentation of the interaction axis iff its image is the threshold in
the other. -/
theorem marginal_transport {L : Set ℝ} (hne : L.Nonempty) (hbd : BddBelow L) {a : ℝ}
    (ha : 0 < a) (b t₀ : ℝ) :
    t₀ = sInf L ↔ a * t₀ + b = sInf ((fun x => a * x + b) '' L) := by
  rw [csInf_image_affine hne hbd ha b]
  constructor
  · rintro rfl
    rfl
  · intro h
    exact mul_left_cancel₀ ha.ne' (by linarith : a * t₀ = a * sInf L)

end GaloisForLFunctions
