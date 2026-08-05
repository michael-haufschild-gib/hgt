import GaloisForLFunctions.HTGeometry.TranslateJetGroupFullRank

/-!
# Node packets whose row-by-shift family is collision-free

A full-rank node packet is not enough for the translation-rank interfaces: they also demand that the
*combined* family `(r, i) ↦ z r + shift i` be injective.  Row injectivity does not give this — a
collision is `z r − z r' = shift i' − shift i`, one of finitely many forbidden differences.

Restricting the sampled set removes the problem outright.  Sample only on truncated vertical rays
over a spaced subsequence of the carrier's zeros.  Two such nodes are then either on the same ray,
where their difference is purely imaginary of modulus below the truncation height, or on different
rays, where their real parts already differ by more than the spacing.  A forbidden difference whose
modulus lies between the two thresholds is therefore never realized.

Since the carrier's zeros satisfy `n + 3/4 < ζ_n < n + 5/4`, an index spacing of `K` forces a
separation of more than `K − 1/2`.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- Two zeros whose indices are `K`-spaced are separated by more than `K − 1/2`. -/
theorem spacedZero_gap (θ : BoundedRealSequence) (K : ℕ) {a b : ℕ} (hab : a < b) :
    (K : ℝ) - 1 / 2 < movingCanonicalZero θ (b * K) - movingCanonicalZero θ (a * K) := by
  have hstep : a * K + K ≤ b * K := by
    calc a * K + K = (a + 1) * K := by ring
      _ ≤ b * K := Nat.mul_le_mul_right K hab
  have hcast : ((a * K : ℕ) : ℝ) + (K : ℝ) ≤ ((b * K : ℕ) : ℝ) := by exact_mod_cast hstep
  have h1 := movingCanonicalZero_lower θ (b * K)
  have h2 := movingCanonicalZero_upper θ (a * K)
  linarith

/-- Nodes on truncated vertical rays over a `K`-spaced subsequence of the carrier's zeros. -/
noncomputable def spacedRayNodes (θ : BoundedRealSequence) (σ₀ : ℂ) (K : ℕ) (ε : ℝ) : Set ℂ :=
  {w | ∃ (j : ℕ) (y : ℝ), 0 < y ∧ y < ε ∧
      w = ((movingCanonicalZero θ (j * K) : ℂ) - σ₀) + (y : ℂ) * Complex.I}

/-- The base points of the sampled rays. -/
noncomputable def spacedRayBase (θ : BoundedRealSequence) (σ₀ : ℂ) (K : ℕ) : Set ℂ :=
  Set.range fun j : ℕ => ((movingCanonicalZero θ (j * K) : ℂ) - σ₀)

theorem injective_spacedRayBase (θ : BoundedRealSequence) (σ₀ : ℂ) {K : ℕ} (hK : 0 < K) :
    Function.Injective fun j : ℕ => ((movingCanonicalZero θ (j * K) : ℂ) - σ₀) := by
  intro j₁ j₂ hj
  have hre : movingCanonicalZero θ (j₁ * K) - σ₀.re
      = movingCanonicalZero θ (j₂ * K) - σ₀.re := by
    simpa using congrArg Complex.re hj
  have hz : movingCanonicalZero θ (j₁ * K) = movingCanonicalZero θ (j₂ * K) := by linarith
  have hmul : j₁ * K = j₂ * K := movingCanonicalZero_injective θ hz
  exact Nat.eq_of_mul_eq_mul_right hK hmul

theorem infinite_spacedRayBase (θ : BoundedRealSequence) (σ₀ : ℂ) {K : ℕ} (hK : 0 < K) :
    (spacedRayBase θ σ₀ K).Infinite :=
  Set.infinite_range_of_injective (injective_spacedRayBase θ σ₀ hK)

theorem infinite_spacedRayNodes (θ : BoundedRealSequence) (σ₀ : ℂ) {K : ℕ} {ε : ℝ} (hK : 0 < K)
    (hε : 0 < ε) : (spacedRayNodes θ σ₀ K ε).Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun j : ℕ => ((movingCanonicalZero θ (j * K) : ℂ) - σ₀)
      + ((ε / 2 : ℝ) : ℂ) * Complex.I) ?_ ?_
  · intro j₁ j₂ hj
    exact injective_spacedRayBase θ σ₀ hK (by
      have := congrArg (fun w : ℂ => w - ((ε / 2 : ℝ) : ℂ) * Complex.I) hj
      simpa using this)
  · intro j
    exact ⟨j, ε / 2, by linarith, by linarith, rfl⟩

/-- Nodes over the sampled rays reach every base point vertically. -/
theorem spacedRayNodes_mem_of_base (θ : BoundedRealSequence) (σ₀ : ℂ) (K : ℕ) {ε : ℝ}
    {ζ : ℂ} (hζ : ζ ∈ spacedRayBase θ σ₀ K) :
    ∀ y : ℝ, 0 < y → y < ε → ζ + (y : ℂ) * Complex.I ∈ spacedRayNodes θ σ₀ K ε := by
  obtain ⟨j, rfl⟩ := hζ
  exact fun y hy hyε => ⟨j, y, hy, hyε, rfl⟩

set_option maxHeartbeats 800000 in
/-- **The separation dichotomy.**  Two distinct sampled nodes are either closer than the truncation
height or farther apart than the spacing. -/
theorem spacedRayNodes_dichotomy (θ : BoundedRealSequence) (σ₀ : ℂ) {K : ℕ} {ε : ℝ} (hK : 0 < K)
    {w w' : ℂ} (hw : w ∈ spacedRayNodes θ σ₀ K ε) (hw' : w' ∈ spacedRayNodes θ σ₀ K ε)
    (hne : w ≠ w') :
    ‖w - w'‖ < ε ∨ (K : ℝ) - 1 / 2 < ‖w - w'‖ := by
  obtain ⟨j, y, hy0, hyε, rfl⟩ := hw
  obtain ⟨j', y', hy0', hyε', rfl⟩ := hw'
  by_cases hj : j = j'
  · subst hj
    left
    have hdiff : ((movingCanonicalZero θ (j * K) : ℂ) - σ₀) + (y : ℂ) * Complex.I
        - (((movingCanonicalZero θ (j * K) : ℂ) - σ₀) + (y' : ℂ) * Complex.I)
        = (((y - y' : ℝ)) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [hdiff, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith
  · right
    have hre : (((movingCanonicalZero θ (j * K) : ℂ) - σ₀) + (y : ℂ) * Complex.I
        - (((movingCanonicalZero θ (j' * K) : ℂ) - σ₀) + (y' : ℂ) * Complex.I)).re
        = movingCanonicalZero θ (j * K) - movingCanonicalZero θ (j' * K) := by
      simp
    have habs : (K : ℝ) - 1 / 2 < |movingCanonicalZero θ (j * K)
        - movingCanonicalZero θ (j' * K)| := by
      have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
      rcases lt_or_gt_of_ne hj with h | h
      · have hgap := spacedZero_gap θ K h
        rw [abs_sub_comm, abs_of_pos (by linarith)]
        exact hgap
      · have hgap := spacedZero_gap θ K h
        rw [abs_of_pos (by linarith)]
        exact hgap
    calc (K : ℝ) - 1 / 2 < |movingCanonicalZero θ (j * K) - movingCanonicalZero θ (j' * K)| := habs
      _ = |(((movingCanonicalZero θ (j * K) : ℂ) - σ₀) + (y : ℂ) * Complex.I
            - (((movingCanonicalZero θ (j' * K) : ℂ) - σ₀) + (y' : ℂ) * Complex.I)).re| := by
        rw [hre]
      _ ≤ _ := Complex.abs_re_le_norm _

/-- **The collision-free connector.**  A node packet drawn from the sampled rays makes the whole
row-by-shift family injective, provided every nonzero shift difference has modulus between the
truncation height and the spacing. -/
theorem injective_combined_of_spacedRayNodes {row ι : Type*}
    (θ : BoundedRealSequence) (σ₀ : ℂ) {K : ℕ} {ε : ℝ} (hK : 0 < K)
    (z : row → ℂ) (hzmem : ∀ b, z b ∈ spacedRayNodes θ σ₀ K ε) (hzinj : Function.Injective z)
    (shift : ι → ℂ) (hshiftinj : Function.Injective shift)
    (hlow : ∀ i i' : ι, i ≠ i' → ε ≤ ‖shift i - shift i'‖)
    (hhigh : ∀ i i' : ι, ‖shift i - shift i'‖ ≤ (K : ℝ) - 1 / 2) :
    Function.Injective fun x : row × ι => z x.1 + shift x.2 := by
  rintro ⟨r, i⟩ ⟨r', i'⟩ h
  dsimp only at h
  by_cases hr : r = r'
  · subst hr
    have hs : shift i = shift i' := by linear_combination h
    exact Prod.ext rfl (hshiftinj hs)
  · exfalso
    have hzne : z r ≠ z r' := fun hc => hr (hzinj hc)
    have hii : i ≠ i' := by
      intro hc
      subst hc
      exact hzne (by linear_combination h)
    have hdiff : z r - z r' = shift i' - shift i := by linear_combination h
    have hnorm : ‖z r - z r'‖ = ‖shift i' - shift i‖ := by rw [hdiff]
    rcases spacedRayNodes_dichotomy θ σ₀ hK (hzmem r) (hzmem r') hzne with hlt | hgt
    · rw [hnorm] at hlt
      have := hlow i' i (Ne.symm hii)
      linarith
    · rw [hnorm] at hgt
      have := hhigh i' i
      linarith


/-- Sampled nodes lie strictly above the base line. -/
theorem spacedRayNodes_im_lt {θ : BoundedRealSequence} {σ₀ : ℂ} {K : ℕ} {ε : ℝ} {w : ℂ}
    (hw : w ∈ spacedRayNodes θ σ₀ K ε) : -σ₀.im < w.im := by
  obtain ⟨j, y, hy0, _, rfl⟩ := hw
  simp only [Complex.add_im, Complex.sub_im, Complex.ofReal_im, zero_sub, Complex.mul_im,
    Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero]
  linarith

/-! ## Jets at integer heights -/

/-- Shifts at the integer heights of the imaginary axis. -/
noncomputable def integerHeightShift (n : ℕ) : Fin (n + 1) → ℂ :=
  fun i => ((i : ℕ) : ℂ) * Complex.I

@[simp] theorem integerHeightShift_im (n : ℕ) (i : Fin (n + 1)) :
    (integerHeightShift n i).im = ((i : ℕ) : ℝ) := by
  simp [integerHeightShift]

@[simp] theorem integerHeightShift_zero (n : ℕ) : integerHeightShift n 0 = 0 := by
  simp [integerHeightShift]

theorem integerHeightShift_injective (n : ℕ) : Function.Injective (integerHeightShift n) := by
  intro i i' h
  have him : ((i : ℕ) : ℝ) = ((i' : ℕ) : ℝ) := by
    simpa using congrArg Complex.im h
  exact Fin.ext (by exact_mod_cast him)

theorem norm_integerHeightShift_sub (n : ℕ) (i i' : Fin (n + 1)) :
    ‖integerHeightShift n i - integerHeightShift n i'‖ = |((i : ℕ) : ℝ) - ((i' : ℕ) : ℝ)| := by
  have h : integerHeightShift n i - integerHeightShift n i'
      = ((((i : ℕ) : ℝ) - ((i' : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I := by
    rw [integerHeightShift, integerHeightShift]
    push_cast
    ring
  rw [h, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

theorem one_le_norm_integerHeightShift_sub (n : ℕ) {i i' : Fin (n + 1)} (hii : i ≠ i') :
    (1 : ℝ) ≤ ‖integerHeightShift n i - integerHeightShift n i'‖ := by
  rw [norm_integerHeightShift_sub]
  have hne : (i : ℕ) ≠ (i' : ℕ) := fun hc => hii (Fin.ext hc)
  rcases Nat.lt_or_ge (i : ℕ) (i' : ℕ) with h | h
  · have h1 : ((i : ℕ) : ℝ) + 1 ≤ ((i' : ℕ) : ℝ) := by exact_mod_cast h
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  · have hgt : (i' : ℕ) < (i : ℕ) := lt_of_le_of_ne h (Ne.symm hne)
    have h1 : ((i' : ℕ) : ℝ) + 1 ≤ ((i : ℕ) : ℝ) := by exact_mod_cast hgt
    rw [abs_of_nonneg (by linarith)]
    linarith

theorem norm_integerHeightShift_sub_le (n : ℕ) (i i' : Fin (n + 1)) :
    ‖integerHeightShift n i - integerHeightShift n i'‖ ≤ ((n + 1 : ℕ) : ℝ) - 1 / 2 := by
  rw [norm_integerHeightShift_sub]
  have hi : ((i : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.lt_succ_iff.mp i.isLt
  have hi' : ((i' : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.lt_succ_iff.mp i'.isLt
  have h0 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
  have h0' : (0 : ℝ) ≤ ((i' : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [abs_le]
  push_cast
  constructor <;> linarith

/-- The height assignment of the jets, the distinguished slot pinned to the real axis. -/
def groupHeightIdx {M n : ℕ} (height : Fin (M + 1) → Fin (n + 1)) : Fin (M + 1) → Fin (n + 1) :=
  fun k => if k = 0 then 0 else height k

@[simp] theorem groupHeightIdx_zero {M n : ℕ} (height : Fin (M + 1) → Fin (n + 1)) :
    groupHeightIdx height 0 = 0 := by
  simp [groupHeightIdx]

/-- The box climbs on the ground group and descends on every raised jet. -/
noncomputable def integerHeightBox {M n : ℕ} (height : Fin (M + 1) → Fin (n + 1)) (N : ℕ)
    (a : Fin (N + 1)) : Fin (M + 1) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm
    (fun k => if groupHeightIdx height k = 0 then (a : ℕ) else N - (a : ℕ))

@[simp] theorem integerHeightBox_apply {M n : ℕ} (height : Fin (M + 1) → Fin (n + 1)) (N : ℕ)
    (a : Fin (N + 1)) (k : Fin (M + 1)) :
    integerHeightBox height N a k
      = if groupHeightIdx height k = 0 then (a : ℕ) else N - (a : ℕ) := by
  simp [integerHeightBox]

set_option maxHeartbeats 1000000 in
/-- **Unconditional.**  A node packet that meets every condition the translation-rank interfaces
impose: the nodes are pairwise distinct, the whole row-by-shift family is collision-free, every
shifted node lies in the open upper half-plane, and the expanded evaluation map of the height box is
injective.

Arbitrarily many jets sit at arbitrarily many integer heights, arbitrarily many of them sharing the
ground level, each differentiated to its own order. -/
theorem exists_row_packet_integerHeights_combinedInjective
    (θ : BoundedRealSequence) (M n q N : ℕ) (m : Fin (M + 1) → ℕ)
    (height : Fin (M + 1) → Fin (n + 1)) :
    ∃ z : (Fin (N + 1) × Fin (q + 1)) → ℂ,
      Function.Injective z ∧
      Function.Injective (fun x : (Fin (N + 1) × Fin (q + 1)) × Fin (n + 1) =>
        z x.1 + integerHeightShift n x.2) ∧
      (∀ x : (Fin (N + 1) × Fin (q + 1)) × Fin (n + 1),
        0 < (z x.1 + integerHeightShift n x.2).im) ∧
      Function.Injective (expandedDifferentialEvaluationMatrix q (M + 1) z
        (integerHeightBox height N)
        (fun p => iteratedDeriv (m p.2) (movingCanonicalLogDerivative θ)
          (z p.1 + integerHeightShift n (groupHeightIdx height p.2)))).mulVec := by
  classical
  have hKpos : 0 < n + 1 := Nat.succ_pos n
  have hσ0 : integerHeightShift n (groupHeightIdx height 0) = 0 := by simp
  have hkey : ∀ k : Fin (M + 1),
      integerHeightShift n (groupHeightIdx height k)
          = integerHeightShift n (groupHeightIdx height 0) ↔ groupHeightIdx height k = 0 := by
    intro k
    constructor
    · intro h
      have h' : integerHeightShift n (groupHeightIdx height k) = integerHeightShift n 0 := by
        rw [h, groupHeightIdx_zero]
      exact integerHeightShift_injective n h'
    · intro h
      rw [h, groupHeightIdx_zero]
  have hshift : ∀ k : Fin (M + 1),
      integerHeightShift n (groupHeightIdx height k)
          ≠ integerHeightShift n (groupHeightIdx height 0) →
      (integerHeightShift n (groupHeightIdx height 0)).im
        < (integerHeightShift n (groupHeightIdx height k)).im := by
    intro k hk
    have hne : groupHeightIdx height k ≠ 0 := fun h => hk ((hkey k).mpr h)
    rw [integerHeightShift_im, integerHeightShift_im, groupHeightIdx_zero]
    have hpos : 0 < ((groupHeightIdx height k : Fin (n + 1)) : ℕ) := by
      refine Nat.pos_of_ne_zero fun h => hne ?_
      exact Fin.ext h
    have : (0 : ℝ) < ((groupHeightIdx height k : Fin (n + 1)) : ℕ) := by exact_mod_cast hpos
    simpa using this
  have hmono : ∀ k : Fin (M + 1),
      integerHeightShift n (groupHeightIdx height k)
          = integerHeightShift n (groupHeightIdx height 0) →
      Monotone fun a : Fin (N + 1) => integerHeightBox height N a k := by
    intro k hk a b hab
    have h0 : groupHeightIdx height k = 0 := (hkey k).mp hk
    show integerHeightBox height N a k ≤ integerHeightBox height N b k
    rw [integerHeightBox_apply, integerHeightBox_apply, if_pos h0, if_pos h0]
    exact hab
  have hanti : ∀ k : Fin (M + 1),
      integerHeightShift n (groupHeightIdx height k)
          ≠ integerHeightShift n (groupHeightIdx height 0) →
      Antitone fun a : Fin (N + 1) => integerHeightBox height N a k := by
    intro k hk a b hab
    have hne : groupHeightIdx height k ≠ 0 := fun h => hk ((hkey k).mpr h)
    show integerHeightBox height N b k ≤ integerHeightBox height N a k
    rw [integerHeightBox_apply, integerHeightBox_apply, if_neg hne, if_neg hne]
    exact Nat.sub_le_sub_left hab N
  have hstrict : StrictMono fun a : Fin (N + 1) => integerHeightBox height N a 0 := by
    intro a b hab
    show integerHeightBox height N a 0 < integerHeightBox height N b 0
    rw [integerHeightBox_apply, integerHeightBox_apply, groupHeightIdx_zero, if_pos rfl,
      if_pos rfl]
    exact hab
  have hzero : ∀ ζ ∈ spacedRayBase θ 0 (n + 1), ∃ p : ℕ,
      ζ = (movingCanonicalZero θ p : ℂ) - integerHeightShift n (groupHeightIdx height 0) := by
    rintro ζ ⟨j, rfl⟩
    exact ⟨j * (n + 1), by rw [hσ0]⟩
  obtain ⟨z, hzmem, hzinj, hrank⟩ := exists_row_packet_in_set_minimalShiftGroup_signedBox
    (κ := Fin (N + 1)) (row := Fin (N + 1) × Fin (q + 1)) (q := q)
    (S := spacedRayNodes θ 0 (n + 1) 1) (Z := spacedRayBase θ 0 (n + 1)) (ε := 1)
    θ m (fun k => integerHeightShift n (groupHeightIdx height k)) 0 (integerHeightBox height N)
    one_pos (infinite_spacedRayNodes θ 0 hKpos one_pos) (infinite_spacedRayBase θ 0 hKpos)
    (fun ζ hζ => spacedRayNodes_mem_of_base θ 0 (n + 1) hζ) hzero hshift hmono hanti hstrict
    id Function.injective_id
  refine ⟨z, hzinj, ?_, ?_, hrank⟩
  · exact injective_combined_of_spacedRayNodes θ 0 hKpos z hzmem hzinj
      (integerHeightShift n) (integerHeightShift_injective n)
      (fun i i' hii => one_le_norm_integerHeightShift_sub n hii)
      (fun i i' => norm_integerHeightShift_sub_le n i i')
  · rintro ⟨b, i⟩
    have hb := spacedRayNodes_im_lt (hzmem b)
    have hi : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
    simp only [Complex.add_im, integerHeightShift_im]
    simp only [Complex.zero_im, neg_zero] at hb
    linarith

end GaloisForLFunctions.HTGeometry
