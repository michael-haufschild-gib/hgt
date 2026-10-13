import GaloisForLFunctions.RHTower.XiSliceEventualPositivityFiniteOffLine

/-!
# Eventual Hadamard positivity reads the asymptotic abscissa

RH is equivalent to `Re (ξ'/ξ)(s) ≥ 0` on the half-plane `Re s > ½`.  Its large-height forms on
the shifted half-planes `Re s > ½ + h` are

`EventualHadamardPositivityRight σ`: there is `T` with `Re (ξ'/ξ)(s) ≥ 0` whenever `Re s > σ` and
`|Im s| ≥ T`.

**Theorem** (`eventualHadamardPositivityRight_iff`).  For `h ≥ 0`, eventual positivity on
`Re s > ½ + h` holds iff only finitely many zeros of `ξ` satisfy `Re ρ > ½ + h`.

So the infimal abscissa of eventual Hadamard positivity is `½ + Θ`, where `Θ` is the limit
superior of `Re ρ − ½` as the height grows.  At `h = 0` this is the finite off-line rung
(`eventualHadamardPositivityRight_half_iff_finiteOffLine`): `Re (ξ'/ξ) ≥ 0` on the whole open
half-plane `Re s > ½` above some height iff only finitely many zeros lie off the critical line.

**Proof.**
* A zero `ρ` obstructs at `s` only inside the disc `(β − ½)² ≥ (Re s − ½)² + (Im s − γ)²`
  (`re_logDeriv_xi_nonneg_of_disk_bound`).  Zeros with `|β − ½| ≤ h` never obstruct on
  `Re s > ½ + h`.  The finitely many others have bounded ordinate, and their discs have radius
  `< ½`, so they are far from `s` once `|Im s|` is large.  Deep zeros on the left are reflected to
  the right by `ρ ↦ 1 − ρ`.
* Conversely, near a zero `ρ₀` of order `m`, `(ξ'/ξ)(ρ₀ − ε) = −m/ε + O(1)`
  (`exists_re_logDeriv_xi_neg_near_zero`).  A zero with `Re ρ₀ > ½ + h` and large ordinate
  therefore violates positivity at a point of `Re s > ½ + h` with the same ordinate.
-/

open Complex Set

namespace RHTower.BacklundConverse

open RHTower.LindelofSparse RHTower.CosineSparseCluster RHTower.DeBruijn RHTower.CosineDefectBudget

noncomputable section

/-- `Re (ξ'/ξ)(s) ≥ 0` on the open half-plane `Re s > σ` at every large height. -/
def EventualHadamardPositivityRight (σ : ℝ) : Prop :=
  ∃ T : ℝ, ∀ s : ℂ, σ < s.re → T ≤ |s.im| → 0 ≤ (logDeriv xi s).re

/-- Zeros right of `½ + h` and their reflections exhaust the zeros at distance `> h` from the
line. -/
theorem finite_abs_spectral_im_gt_of_finite_re_gt {h : ℝ}
    (hF : {q : XiZeroCopy | 1 / 2 + h < ((q.1 : ℂ)).re}.Finite) :
    {q : XiZeroCopy | h < |(xiSpectralPoint q).im|}.Finite := by
  refine (hF.union (hF.preimage xiZeroCopyReflectEquiv.symm.injective.injOn)).subset
    fun q hq => ?_
  simp only [mem_setOf_eq] at hq
  have hsp := spectral_im_eq q
  rcases lt_abs.mp hq with h1 | h1
  · right
    show 1 / 2 + h < (((xiZeroCopyReflectEquiv.symm q).1 : ℂ)).re
    have hr := spectral_im_eq (xiZeroCopyReflectEquiv.symm q)
    rw [xiSpectralPoint_reflect_symm, Complex.neg_im] at hr
    linarith
  · left
    show 1 / 2 + h < ((q.1 : ℂ)).re
    linarith

/-- **The Hadamard receiver reads the asymptotic abscissa.**  For `h ≥ 0`, `Re (ξ'/ξ) ≥ 0` on
`Re s > ½ + h` at every large height iff only finitely many zeros have `Re ρ > ½ + h`. -/
theorem eventualHadamardPositivityRight_iff {h : ℝ} (hh : 0 ≤ h) :
    EventualHadamardPositivityRight (1 / 2 + h) ↔
      {q : XiZeroCopy | 1 / 2 + h < ((q.1 : ℂ)).re}.Finite := by
  constructor
  · rintro ⟨T, hT⟩
    -- every zero right of `½ + h` has ordinate below `T`
    have hbound : ∀ q : XiZeroCopy, 1 / 2 + h < ((q.1 : ℂ)).re → |((q.1 : ℂ)).im| < T := by
      intro q hq
      by_contra hge
      rw [not_lt] at hge
      obtain ⟨ε, hε0, hεδ, hneg⟩ := exists_re_logDeriv_xi_neg_near_zero
        (xi_xiZeroCopy_eq_zero q) (δ := ((q.1 : ℂ)).re - (1 / 2 + h)) (by linarith)
      have hre : 1 / 2 + h < ((q.1 : ℂ) - ε).re := by
        simp only [Complex.sub_re, Complex.ofReal_re]; linarith
      have him : T ≤ |((q.1 : ℂ) - ε).im| := by
        simp only [Complex.sub_im, Complex.ofReal_im, sub_zero]; exact hge
      linarith [hT _ hre him]
    refine (xiZeroBall (⌈|T| + 1⌉₊)).finite_toSet.subset fun q hq => ?_
    simp only [Finset.mem_coe, mem_xiZeroBall]
    have h1 := Complex.norm_le_abs_re_add_abs_im (xiSpectralPoint q)
    have h2 := abs_spectral_im_lt_half q
    have h3 : |T| + 1 ≤ (⌈|T| + 1⌉₊ : ℝ) := Nat.le_ceil _
    have h4 : |(xiSpectralPoint q).re| < |T| := by
      rw [spectral_re_eq]; exact (hbound q hq).trans_le (le_abs_self T)
    linarith
  · intro hF
    set E : Set XiZeroCopy := {q | h < |(xiSpectralPoint q).im|} with hE
    have hEfin : E.Finite := finite_abs_spectral_im_gt_of_finite_re_gt hF
    obtain ⟨M, hM⟩ := (hEfin.image fun q => |((q.1 : ℂ)).im|).bddAbove
    refine ⟨M + 1, fun s hs hT => ?_⟩
    by_cases hxi : xi s = 0
    · rw [logDeriv_xi_eq_zero_of_xi_eq_zero hxi, Complex.zero_re]
    refine re_logDeriv_xi_nonneg_of_disk_bound (by linarith) hxi fun q => ?_
    have hspec := abs_spectral_im_lt_half q
    rw [spectral_im_eq] at hspec
    have hhalf : (((q.1 : ℂ)).re - 1 / 2) ^ 2 < 1 / 4 := by
      have : |((q.1 : ℂ)).re - 1 / 2| < 1 / 2 := by rw [abs_sub_comm]; exact hspec
      nlinarith [abs_nonneg (((q.1 : ℂ)).re - 1 / 2), sq_abs (((q.1 : ℂ)).re - 1 / 2)]
    by_cases hq : q ∈ E
    · -- a deep zero: its ordinate is bounded, so it is far from `s`
      have hγ : |((q.1 : ℂ)).im| ≤ M := hM ⟨q, hq, rfl⟩
      have hfar : 1 ≤ |s.im - ((q.1 : ℂ)).im| := by
        have := abs_sub_abs_le_abs_sub s.im ((q.1 : ℂ)).im
        linarith
      have h1 : 1 ≤ (s.im - ((q.1 : ℂ)).im) ^ 2 := by
        nlinarith [sq_abs (s.im - ((q.1 : ℂ)).im)]
      nlinarith [sq_nonneg (s.re - 1 / 2)]
    · -- a zero within `h` of the line never obstructs on `Re s > ½ + h`
      simp only [hE, mem_setOf_eq, not_lt, spectral_im_eq] at hq
      rw [abs_sub_comm] at hq
      have h1 : (((q.1 : ℂ)).re - 1 / 2) ^ 2 ≤ h ^ 2 := by
        nlinarith [sq_abs (((q.1 : ℂ)).re - 1 / 2), abs_nonneg (((q.1 : ℂ)).re - 1 / 2)]
      have h2 : h ^ 2 < (s.re - 1 / 2) ^ 2 := by
        have : h < s.re - 1 / 2 := by linarith
        nlinarith
      nlinarith [sq_nonneg (s.im - ((q.1 : ℂ)).im)]

/-- Finitely many zeros right of the line is finitely many zeros off the line. -/
theorem finite_re_gt_half_iff_finiteOffLine :
    {q : XiZeroCopy | 1 / 2 < ((q.1 : ℂ)).re}.Finite ↔ FiniteOffLine := by
  constructor
  · intro hF
    have hF' : {q : XiZeroCopy | 1 / 2 + 0 < ((q.1 : ℂ)).re}.Finite := by
      simpa only [add_zero] using hF
    refine (finite_abs_spectral_im_gt_of_finite_re_gt hF').subset fun q hq => ?_
    simp only [mem_setOf_eq] at hq ⊢
    exact abs_pos.mpr hq
  · intro hF
    refine hF.subset fun q hq => ?_
    simp only [mem_setOf_eq] at hq ⊢
    rw [spectral_im_eq]
    linarith

/-- **Eventual Hadamard positivity on the whole open half-plane is "finitely many off-line
zeros".** -/
theorem eventualHadamardPositivityRight_half_iff_finiteOffLine :
    EventualHadamardPositivityRight (1 / 2) ↔ FiniteOffLine := by
  have h := eventualHadamardPositivityRight_iff (h := 0) le_rfl
  simp only [add_zero] at h
  rw [h, finite_re_gt_half_iff_finiteOffLine]

end

end RHTower.BacklundConverse
