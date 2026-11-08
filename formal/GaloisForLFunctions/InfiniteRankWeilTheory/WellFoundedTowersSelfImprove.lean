import GaloisForLFunctions.InfiniteRankWeilTheory.TheExceptionalRankDecidesTheWindow

/-!
# Well-founded towers self-improve: the infinite-rank analogue of `|α| ≤ √q`

On a curve, power sums of `2g` numbers that are `O(1)` at every level have every number in the closed
unit disc, and the functional equation puts it on the circle. At infinite rank the statement needs a
hypothesis on the outer part: it is **well-founded above `ρ`** if only finitely many modes lie above
every radius `> ρ` (`WellFoundedAbove`). For the towers of `ζ` at `ρ = 1` this is ZAL; for a curve it
is automatic.

* `mergedWeight_eq_zero_of_thick_bound`: a well-founded tower whose level sums are `≤ Cρᵛ` on a thick
  set of levels has merged weight `0` at every point of modulus `> ρ`: no visible mode lies outside
  the disc of radius `ρ`, whatever the constant `C` and whatever the rank below `ρ`.
* `WeilTower.mergedWeight_eq_zero_of_norm_ne_one`: with weights compatible with the reflection
  `z ↦ 1/z̄`, a crude bound `|S(ν)| ≤ C` on a thick set of levels leaves only the critical layer
  `|z| = 1` visible. This is the infinite-rank Hasse–Weil principle.
* `CurveDatum.unitary_of_thick_trace_bound`: for a curve datum, traces bounded on a thick set of levels
  force every normalized eigenvalue onto the unit circle (`unitary_of_thick_pointCount_bound`: point
  counts within `C q^{n/2}` of `qⁿ + 1` on a thick set of levels). By `TheRankBarrier` the thick set
  cannot be replaced by a set of density `1 − 1/k`.

Without well-foundedness the statement fails: Wolff configurations
(`ArithmeticCastelnuovoSeveri.exists_symmetric_wolff_toeplitz_blind_configuration`) have accumulating
outer points whose contributions cancel at every level.
-/

open Complex Finset

noncomputable section

namespace GaloisForLFunctions.InfiniteRankWeilTheory

/-- The modes above radius `ρ` are **well-founded**: finitely many above every radius `> ρ`. -/
def WellFoundedAbove {ι : Type*} (z : ι → ℂ) (ρ : ℝ) : Prop :=
  ∀ r : ℝ, ρ < r → {i | r < ‖z i‖}.Finite

/-- Every finite family is well-founded above every radius. -/
theorem wellFoundedAbove_of_finite {ι : Type*} [Finite ι] (z : ι → ℂ) (ρ : ℝ) :
    WellFoundedAbove z ρ := fun _ _ => Set.toFinite _

/-- **Elimination at infinite rank.** In a family well-founded above `ρ ≥ 0`, a bound
`|S(ν)| ≤ Cρᵛ` on a thick set of levels forces merged weight `0` at every point of modulus `> ρ`. -/
theorem mergedWeight_eq_zero_of_thick_bound {ι : Type*} (z b : ι → ℂ)
    (hb : Summable fun i => ‖b i‖) {ρ C : ℝ} (hρ : 0 ≤ ρ) (hwf : WellFoundedAbove z ρ)
    {G : Set ℕ} (hG : Thick G) (hbd : ∀ ν ∈ G, ‖levelSum z b ν‖ ≤ C * ρ ^ ν)
    {i : ι} (hi : ρ < ‖z i‖) (F : Finset ι) (hF : ∀ j, z j = z i → j ∈ F) :
    ∑ j ∈ F with z j = z i, b j = 0 := by
  classical
  by_contra hne
  set r₁ : ℝ := (ρ + ‖z i‖) / 2 with hr₁def
  have hr₁ : ρ < r₁ := by linarith
  have hr₁i : r₁ < ‖z i‖ := by linarith
  have hr₁0 : 0 ≤ r₁ := by linarith
  set A : Finset ι := (hwf r₁ hr₁).toFinset with hAdef
  have hmemA : ∀ j, j ∈ A ↔ r₁ < ‖z j‖ := fun j => by simp [hAdef]
  set mw : ι → ℂ := fun j => ∑ l ∈ A with z l = z j, b l with hmw
  have hmerge : ∀ (S : Finset ι) (j : ι), r₁ < ‖z j‖ → (∀ l, z l = z j → l ∈ S) →
      ∑ l ∈ S with z l = z j, b l = mw j := by
    intro S j hj hS
    have hfil : S.filter (fun l => z l = z j) = A.filter (fun l => z l = z j) := by
      ext l
      simp only [mem_filter]
      constructor
      · rintro ⟨-, hl⟩; exact ⟨(hmemA l).2 (by rw [hl]; exact hj), hl⟩
      · rintro ⟨-, hl⟩; exact ⟨hS l hl, hl⟩
    rw [hfil]
  have hiA : i ∈ A := (hmemA i).2 hr₁i
  have hmwi : mw i ≠ 0 := by rw [← hmerge F i hr₁i hF]; exact hne
  set Vis := A.filter (fun j => mw j ≠ 0) with hVis
  obtain ⟨jm, hjmV, hjm⟩ := Vis.exists_max_image (fun j => ‖z j‖) ⟨i, mem_filter.2 ⟨hiA, hmwi⟩⟩
  set R : ℝ := ‖z jm‖ with hRdef
  have hjmA : jm ∈ A := (mem_filter.1 hjmV).1
  have hR₁ : r₁ < R := (hmemA jm).1 hjmA
  set Ftop := A.filter (fun j => R ≤ ‖z j‖) with hFtop
  set Low := A.filter (fun j => ‖z j‖ < R) with hLow
  obtain ⟨r, hr0, hrR, hr₁r, hrLow⟩ :
      ∃ r : ℝ, 0 ≤ r ∧ r < R ∧ r₁ ≤ r ∧ ∀ j ∈ Low, ‖z j‖ ≤ r := by
    by_cases hL : Low.Nonempty
    · obtain ⟨jl, hjl, hjlmax⟩ := Low.exists_max_image (fun j => ‖z j‖) hL
      refine ⟨max r₁ ‖z jl‖, le_max_of_le_left hr₁0, max_lt hR₁ (mem_filter.1 hjl).2,
        le_max_left _ _, fun j hj => (hjlmax j hj).trans (le_max_right _ _)⟩
    · exact ⟨r₁, hr₁0, hR₁, le_rfl, fun j hj => absurd ⟨j, hj⟩ hL⟩
  have hfibF : ∀ j ∈ Ftop, ∀ l, z l = z j → l ∈ Ftop := by
    intro j hj l hl
    obtain ⟨hjA', hjR⟩ := mem_filter.1 hj
    refine mem_filter.2 ⟨(hmemA l).2 ?_, by rw [hl]; exact hjR⟩
    rw [hl]; exact (hmemA j).1 hjA'
  have hrest : ∀ j ∉ Ftop, ‖z j‖ ≤ r := by
    intro j hj
    by_cases hjA : j ∈ A
    · have hlt : ‖z j‖ < R := by
        by_contra hge; push Not at hge; exact hj (mem_filter.2 ⟨hjA, hge⟩)
      exact hrLow j (mem_filter.2 ⟨hjA, hlt⟩)
    · have : ‖z j‖ ≤ r₁ := by by_contra h; push Not at h; exact hjA ((hmemA j).2 h)
      linarith
  have htop : ∀ j ∈ Ftop, (∑ l ∈ Ftop with z l = z j, b l) ≠ 0 → ‖z j‖ = R := by
    intro j hj hne'
    obtain ⟨hjA', hjR⟩ := mem_filter.1 hj
    rw [hmerge Ftop j ((hmemA j).1 hjA') (hfibF j hj)] at hne'
    exact le_antisymm (hjm j (mem_filter.2 ⟨hjA', hne'⟩)) hjR
  have hvis : ∃ j ∈ Ftop, (∑ l ∈ Ftop with z l = z j, b l) ≠ 0 := by
    have hjmF : jm ∈ Ftop := mem_filter.2 ⟨hjmA, le_rfl⟩
    refine ⟨jm, hjmF, ?_⟩
    rw [hmerge Ftop jm hR₁ (hfibF jm hjmF)]
    exact (mem_filter.1 hjmV).2
  exact not_forall_mem_thick_norm_levelSum_le z b hb Ftop (by linarith) hr0 hrR hrest htop hvis
    hρ (by linarith) hG hbd

/-- **The infinite-rank Hasse–Weil principle.** In a Weil tower whose outer part is well-founded, with
weights compatible with the reflection, a crude bound `|S(ν)| ≤ C` on a thick set of levels leaves
only the critical layer visible: every point off the unit circle has merged weight `0`. -/
theorem WeilTower.mergedWeight_eq_zero_of_norm_ne_one {ι : Type*} (T : WeilTower ι) {b : ι → ℂ}
    (hb : Summable fun i => ‖b i‖) (hrefl : ∀ i, b (T.reflPerm i) = starRingEnd ℂ (b i))
    (hwf : WellFoundedAbove T.z 1) {G : Set ℕ} (hG : Thick G) {C : ℝ}
    (hbd : ∀ ν ∈ G, ‖levelSum T.z b ν‖ ≤ C) {i : ι} (hi : ‖T.z i‖ ≠ 1) (F : Finset ι)
    (hF : ∀ j, T.z j = T.z i → j ∈ F) :
    ∑ j ∈ F with T.z j = T.z i, b j = 0 := by
  classical
  have hbd' : ∀ ν ∈ G, ‖levelSum T.z b ν‖ ≤ C * 1 ^ ν := fun ν hν => by
    rw [one_pow, mul_one]; exact hbd ν hν
  rcases lt_or_gt_of_ne hi with hlt | hgt
  · -- an inner point: reflect it to the outer point `1/z̄`
    set i' := T.reflPerm i
    have hpos : 0 < ‖T.z i‖ := norm_pos_iff.mpr (T.z_ne_zero i)
    have hi' : 1 < ‖T.z i'‖ := by rw [T.norm_z_reflPerm]; exact one_lt_inv₀ hpos |>.mpr hlt
    have hzr : ∀ a c : ι, T.z (T.reflPerm a) = T.z (T.reflPerm c) ↔ T.z a = T.z c := by
      intro a c
      rw [T.z_reflPerm, T.z_reflPerm, inv_inj, (starRingEnd ℂ).injective.eq_iff]
    have hF' : ∀ j, T.z j = T.z i' → j ∈ F.image T.reflPerm := by
      intro j hj
      refine mem_image.2 ⟨T.reflPerm.symm j, hF _ ?_, T.reflPerm.apply_symm_apply j⟩
      rw [← hzr, T.reflPerm.apply_symm_apply]; exact hj
    have h0 := mergedWeight_eq_zero_of_thick_bound T.z b hb zero_le_one hwf hG hbd' hi'
      (F.image T.reflPerm) hF'
    rw [Finset.filter_image, Finset.sum_image (fun a _ c _ h => T.reflPerm.injective h)] at h0
    have hfil : (F.filter fun a => T.z (T.reflPerm a) = T.z i') =
        F.filter fun a => T.z a = T.z i := by
      ext a; simp only [mem_filter, i', hzr]
    rw [hfil] at h0
    simp_rw [hrefl] at h0
    rw [← map_sum, map_eq_zero] at h0
    exact h0
  · exact mergedWeight_eq_zero_of_thick_bound T.z b hb zero_le_one hwf hG hbd' hgt F hF

/-! ### Curves -/

section Curves

open ArithmeticCastelnuovoSeveri

variable {ι : Type*} [Fintype ι]

/-- **Curves self-improve on thick sets of levels.** If the traces of a curve datum are bounded on a
thick set of levels, every normalized eigenvalue is on the unit circle. -/
theorem _root_.GaloisForLFunctions.ArithmeticCastelnuovoSeveri.CurveDatum.unitary_of_thick_trace_bound
    (D : CurveDatum ι) {G : Set ℕ} (hG : Thick G) {C : ℝ}
    (hbd : ∀ n ∈ G, |D.trace n| ≤ C) (i : ι) : ‖D.β i‖ = 1 := by
  classical
  have hlev : ∀ n ∈ G, ‖levelSum D.toWeilTower.z (fun _ => 1) n‖ ≤ C * 1 ^ n := by
    intro n hn
    rw [levelSum_toWeilTower_one, D.powerSum_eq_trace, Complex.norm_real, Real.norm_eq_abs,
      one_pow, mul_one]
    exact hbd n hn
  have hle : ∀ j, ‖D.β j‖ ≤ 1 := by
    intro j
    by_contra hgt
    push Not at hgt
    have h0 := mergedWeight_eq_zero_of_thick_bound D.toWeilTower.z (fun _ => (1 : ℂ))
      (by simp) zero_le_one (wellFoundedAbove_of_finite _ _) hG hlev hgt univ
      (fun _ _ => mem_univ _)
    have hpos : (0 : ℝ) < ((univ.filter fun l => D.β l = D.β j).card : ℝ) := by
      exact_mod_cast card_pos.2 ⟨j, mem_filter.2 ⟨mem_univ _, rfl⟩⟩
    simp only [sum_const, nsmul_eq_mul, mul_one] at h0
    change ((univ.filter fun l => D.β l = D.β j).card : ℂ) = 0 at h0
    exact hpos.ne' (by exact_mod_cast h0)
  have hfe := congrArg norm (D.β_fePerm i)
  rw [norm_mul, norm_one] at hfe
  nlinarith [norm_nonneg (D.β i), norm_nonneg (D.β (D.fePerm i)), hle i, hle (D.fePerm i)]

/-- **Point counts on a thick set of levels.** If `|N_n − qⁿ − 1| ≤ C q^{n/2}` on a thick set of
levels, the datum satisfies the Riemann hypothesis. -/
theorem _root_.GaloisForLFunctions.ArithmeticCastelnuovoSeveri.CurveDatum.unitary_of_thick_pointCount_bound
    (D : CurveDatum ι) {G : Set ℕ} (hG : Thick G) {C : ℝ}
    (hbd : ∀ n ∈ G, |D.pointCount n - (D.q ^ n + 1)| ≤ C * D.sqrtq ^ n) (i : ι) :
    ‖D.β i‖ = 1 := by
  refine D.unitary_of_thick_trace_bound hG (C := C) (fun n hn => ?_) i
  have h := hbd n hn
  have hpos : 0 < D.sqrtq ^ n := pow_pos D.sqrtq_pos n
  rw [show D.pointCount n - (D.q ^ n + 1) = -(D.sqrtq ^ n * D.trace n) by
    simp only [CurveDatum.pointCount]; ring, abs_neg, abs_mul, abs_of_pos hpos] at h
  nlinarith

end Curves

end GaloisForLFunctions.InfiniteRankWeilTheory
