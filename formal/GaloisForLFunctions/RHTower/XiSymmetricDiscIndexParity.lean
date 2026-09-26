import GaloisForLFunctions.RHTower.XiRightDiscPhaseIndexRiemannHypothesis
import GaloisForLFunctions.RHTower.WeightMismatchRefutation

/-!
# Parity of the Hardy index on discs symmetric about the critical line

Let `D = closedBall c t` have its centre on the critical line, `Re c = 1/2`, with `xi ≠ 0` on the
boundary circle.  The reflection `ρ ↦ 1 − conj ρ` maps `D` onto itself and the zero set of `xi` onto
itself, preserving multiplicities (`xi_orderAt_quadruple_eq`).  It fixes exactly the zeros on the
critical line.  Hence the multiplicities of the off-line zeros inside `D` add up to an even number.

* `even_xiDiscRelativeIndex_sub_onLine`: the Hardy relative index of the `xi` boundary phase
  (= the zero count, `DiscArgumentDatum.relativeIndex_eq_zeroCount`) minus the multiplicity count
  of on-line zeros inside `D` is even.
* `onLine_of_index_sub_lt_two`: consequently, a bound `< 2` on that difference forces it to
  vanish, so every zero of `xi` inside `D` lies on the critical line.

On symmetric discs the route-1 integer is therefore "on-line count + an even excess".  To produce
the seam criterion there, it suffices to bound the excess by `1`; the target is a sub-quantum
bound of size `2`, not exact vanishing.
-/

noncomputable section

open Complex Metric

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- The reflection across the critical line. -/
def criticalReflect (ρ : ℂ) : ℂ := 1 - starRingEnd ℂ ρ

theorem criticalReflect_involutive (ρ : ℂ) : criticalReflect (criticalReflect ρ) = ρ := by
  simp [criticalReflect]

theorem criticalReflect_eq_self_iff (ρ : ℂ) : criticalReflect ρ = ρ ↔ ρ.re = 1 / 2 := by
  constructor
  · intro h
    have := congrArg Complex.re h
    simp [criticalReflect] at this
    linarith
  · intro h
    apply Complex.ext
    · simp [criticalReflect, h]; norm_num
    · simp [criticalReflect]

theorem dist_criticalReflect {c : ℂ} (hc : c.re = 1 / 2) (ρ : ℂ) :
    dist (criticalReflect ρ) c = dist ρ c := by
  rw [dist_eq_norm, dist_eq_norm]
  have h : criticalReflect ρ - c = -starRingEnd ℂ (ρ - criticalReflect c) := by
    simp only [criticalReflect, map_sub, map_one, Complex.conj_conj]; ring
  have hcc : criticalReflect c = c := (criticalReflect_eq_self_iff c).mpr hc
  rw [h, hcc, norm_neg, Complex.norm_conj]

theorem zeroMult_criticalReflect (ρ : ℂ) :
    zeroMult xi (criticalReflect ρ) = zeroMult xi ρ := by
  unfold zeroMult criticalReflect
  rw [(xi_orderAt_quadruple_eq ρ).2.2]

theorem xi_criticalReflect_eq_zero {ρ : ℂ} (h : xi ρ = 0) : xi (criticalReflect ρ) = 0 := by
  have hconj : xi (starRingEnd ℂ ρ) = starRingEnd ℂ (xi ρ) := xi_conj ρ
  rw [criticalReflect, xi_one_sub, hconj, h, map_zero]

/-- The zeros of `xi` inside the disc, as the finite set supplied by the argument principle. -/
theorem exists_zeroFinset (c : ℂ) (t : ℝ) (ht : 0 < t) (hne : ∀ ζ ∈ sphere c t, xi ζ ≠ 0) :
    ∃ Z : Finset ℂ, (∀ ρ ∈ Z, ρ ∈ ball c t ∧ xi ρ = 0) ∧ (∀ ρ ∈ ball c t, xi ρ = 0 → ρ ∈ Z) := by
  obtain ⟨Z, hZball, hZzero, -⟩ := (xiDiscDatum c t ht hne).relativeIndex_eq_zeroCount
  exact ⟨Z, fun ρ hρ => ⟨hZball ρ hρ, (hZzero ρ (hZball ρ hρ)).mpr hρ⟩,
    fun ρ hρ h0 => (hZzero ρ hρ).mp h0⟩

/-- The index is the multiplicity count over any finite set of exactly the zeros in the disc. -/
theorem xiDiscRelativeIndex_eq_sum (c : ℂ) (t : ℝ) (ht : 0 < t)
    (hne : ∀ ζ ∈ sphere c t, xi ζ ≠ 0) (Z : Finset ℂ)
    (hZ1 : ∀ ρ ∈ Z, ρ ∈ ball c t ∧ xi ρ = 0) (hZ2 : ∀ ρ ∈ ball c t, xi ρ = 0 → ρ ∈ Z) :
    xiDiscRelativeIndex c t ht hne = ∑ ρ ∈ Z, (zeroMult xi ρ : ℤ) := by
  obtain ⟨Z', hZball, hZzero, hidx⟩ := (xiDiscDatum c t ht hne).relativeIndex_eq_zeroCount
  have hZZ : Z' = Z := by
    ext ρ
    constructor
    · intro hρ
      exact hZ2 ρ (hZball ρ hρ) ((hZzero ρ (hZball ρ hρ)).mpr hρ)
    · intro hρ
      exact (hZzero ρ (hZ1 ρ hρ).1).mp (hZ1 ρ hρ).2
  unfold xiDiscRelativeIndex
  rw [hidx, hZZ]
  rfl

/-- **The off-line multiplicity count inside a symmetric disc is even.** -/
theorem even_offLine_sum {c : ℂ} (hc : c.re = 1 / 2) {t : ℝ} (Z : Finset ℂ)
    (hZ1 : ∀ ρ ∈ Z, ρ ∈ ball c t ∧ xi ρ = 0) (hZ2 : ∀ ρ ∈ ball c t, xi ρ = 0 → ρ ∈ Z) :
    Even (∑ ρ ∈ Z.filter (fun ρ => ¬ ρ.re = 1 / 2), (zeroMult xi ρ : ℤ)) := by
  classical
  set Zoff := Z.filter (fun ρ => ¬ ρ.re = 1 / 2) with hZoff
  have hmem : ∀ ρ ∈ Zoff, criticalReflect ρ ∈ Zoff := by
    intro ρ hρ
    rw [hZoff, Finset.mem_filter] at hρ ⊢
    obtain ⟨hρZ, hρre⟩ := hρ
    obtain ⟨hball, hxi⟩ := hZ1 ρ hρZ
    have hball' : criticalReflect ρ ∈ ball c t := by
      rw [mem_ball, dist_criticalReflect hc]; exact hball
    refine ⟨hZ2 _ hball' (xi_criticalReflect_eq_zero hxi), ?_⟩
    intro hre
    apply hρre
    have h2 : (criticalReflect ρ).re = 1 - ρ.re := by simp [criticalReflect]
    rw [h2] at hre
    linarith
  have hZmod : ((∑ ρ ∈ Zoff, (zeroMult xi ρ : ℤ) : ℤ) : ZMod 2) = 0 := by
    push_cast
    refine Finset.sum_involution (fun ρ _ => criticalReflect ρ) ?_ ?_ ?_ ?_
    · intro ρ _
      rw [zeroMult_criticalReflect, ← two_mul]
      have : (2 : ZMod 2) = 0 := rfl
      rw [this, zero_mul]
    · intro ρ hρ _ heq
      rw [hZoff, Finset.mem_filter] at hρ
      exact hρ.2 ((criticalReflect_eq_self_iff ρ).mp heq)
    · intro ρ hρ; exact hmem ρ hρ
    · intro ρ _; exact criticalReflect_involutive ρ
  exact (ZMod.intCast_eq_zero_iff_even).mp (by exact_mod_cast hZmod)

/-- **Parity law.**  On a disc centred on the critical line, the Hardy index minus the on-line
multiplicity count is even. -/
theorem even_xiDiscRelativeIndex_sub_onLine (c : ℂ) (hc : c.re = 1 / 2) (t : ℝ) (ht : 0 < t)
    (hne : ∀ ζ ∈ sphere c t, xi ζ ≠ 0) (Z : Finset ℂ)
    (hZ1 : ∀ ρ ∈ Z, ρ ∈ ball c t ∧ xi ρ = 0) (hZ2 : ∀ ρ ∈ ball c t, xi ρ = 0 → ρ ∈ Z) :
    Even (xiDiscRelativeIndex c t ht hne -
      ∑ ρ ∈ Z.filter (fun ρ => ρ.re = 1 / 2), (zeroMult xi ρ : ℤ)) := by
  classical
  rw [xiDiscRelativeIndex_eq_sum c t ht hne Z hZ1 hZ2,
    ← Finset.sum_filter_add_sum_filter_not Z (fun ρ => ρ.re = 1 / 2), add_sub_cancel_left]
  exact even_offLine_sum hc Z hZ1 hZ2

/-- **Sub-quantum criterion on a symmetric disc.**  If the index exceeds the on-line count by less
than `2`, every zero of `xi` in the disc lies on the critical line. -/
theorem onLine_of_index_sub_lt_two (c : ℂ) (hc : c.re = 1 / 2) (t : ℝ) (ht : 0 < t)
    (hne : ∀ ζ ∈ sphere c t, xi ζ ≠ 0) (Z : Finset ℂ)
    (hZ1 : ∀ ρ ∈ Z, ρ ∈ ball c t ∧ xi ρ = 0) (hZ2 : ∀ ρ ∈ ball c t, xi ρ = 0 → ρ ∈ Z)
    (hlt : xiDiscRelativeIndex c t ht hne -
      ∑ ρ ∈ Z.filter (fun ρ => ρ.re = 1 / 2), (zeroMult xi ρ : ℤ) < 2) :
    ∀ ρ ∈ Z, ρ.re = 1 / 2 := by
  classical
  have hsplit : xiDiscRelativeIndex c t ht hne -
      ∑ ρ ∈ Z.filter (fun ρ => ρ.re = 1 / 2), (zeroMult xi ρ : ℤ) =
      ∑ ρ ∈ Z.filter (fun ρ => ¬ ρ.re = 1 / 2), (zeroMult xi ρ : ℤ) := by
    rw [xiDiscRelativeIndex_eq_sum c t ht hne Z hZ1 hZ2,
      ← Finset.sum_filter_add_sum_filter_not Z (fun ρ => ρ.re = 1 / 2), add_sub_cancel_left]
  rw [hsplit] at hlt
  have heven := even_offLine_sum hc Z hZ1 hZ2
  have hnn : 0 ≤ ∑ ρ ∈ Z.filter (fun ρ => ¬ ρ.re = 1 / 2), (zeroMult xi ρ : ℤ) :=
    Finset.sum_nonneg fun ρ _ => Int.natCast_nonneg _
  have hzero : ∑ ρ ∈ Z.filter (fun ρ => ¬ ρ.re = 1 / 2), (zeroMult xi ρ : ℤ) = 0 := by
    obtain ⟨k, hk⟩ := heven
    omega
  intro ρ hρ
  by_contra hre
  have hmemoff : ρ ∈ Z.filter (fun ρ => ¬ ρ.re = 1 / 2) := Finset.mem_filter.mpr ⟨hρ, hre⟩
  have hpos : (1 : ℤ) ≤ (zeroMult xi ρ : ℤ) := by
    exact_mod_cast one_le_zeroMult_xi (hZ1 ρ hρ).2
  have hle := Finset.single_le_sum
    (f := fun ρ' => (zeroMult xi ρ' : ℤ)) (fun ρ' _ => Int.natCast_nonneg _) hmemoff
  omega

end RHTower
