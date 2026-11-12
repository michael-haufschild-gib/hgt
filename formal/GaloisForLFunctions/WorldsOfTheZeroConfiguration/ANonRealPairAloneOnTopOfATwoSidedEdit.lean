import GaloisForLFunctions.WorldsOfTheZeroConfiguration.TheEditSeriesHasAPrescribedZeroPair
import GaloisForLFunctions.WorldsOfTheZeroConfiguration.TwoSidedPrimeEdits
import GaloisForLFunctions.RHTower.PrimeShortIntervalsSeventeenThirtiethsUnconditional
import GaloisForLFunctions.RHTower.ZetaZeroFreeRegionUnrestricted

/-!
# A non-real pair alone on top of a two-sided edit

A deletion of primes with a count rate has a real fake zero on top
(`SumProductArithmeticOfTheLogarithm.exists_real_fake_zero_of_keptPrimeSystem`), and a system that
only adds primes vanishes at its real abscissa.  A two-sided edit has neither constraint.

**Theorem** (`exists_isEdit_pairTwin`).  Let `1/2 < Re ρ < 14/15`.  The greedy edit of the primes
at the frequency `ρ` (some primes deleted, some doubled) has zeta function

`(s − 1) ζ_B(s) = (s − 1) ζ(s) · C (s − ρ)(s − ρ̄) e^{H(s)}`, `C ≠ 0`, `H` holomorphic on
`Re s > 1/2`

(`IsPairTwin`), and integer count `N_B(x) = A x + O(x^β)` for every `β > Re ρ`.  So the fake zeros
of `B` right of the line are exactly `ρ` and `ρ̄` (`IsPairTwin.hasFakeZeroSet`); for non-real `ρ`
the continuation has no real zero in `(1/2, ∞)` (`IsPairTwin.ne_zero_of_real`); and for
`ζ(ρ) ≠ 0` the system is an integer-norm fake at `β` (`exists_isEdit_fake_with_zero_pair`).

**Corollary** (`exists_isEdit_fake_without_real_zero`).  For every `β > 1/2` there is an
integer-norm fake at `β`, a two-sided edit of the rational primes, whose fake zeros right of the
line are one non-real pair: integer norms, an Euler product over the rational primes with
multiplicities `0, 1, 2` and a power saving of the count do not force a real zero on top of a
finite layer.
-/

open Complex Filter Topology
open RHTower RHTower.BeurlingDeletion GaloisForLFunctions.RigidArithmeticOfCuts
open GaloisForLFunctions.SumProductArithmeticOfTheLogarithm

noncomputable section

namespace GaloisForLFunctions.WorldsOfTheZeroConfiguration

open PrimeEdits TwoSidedEdits

/-- `B` is a **pair twin of `ζ` at `ρ`**: `(s − 1) ζ_B(s) = (s − 1) ζ(s) · C (s − ρ)(s − ρ̄) e^{H(s)}`
with `C ≠ 0` and `H` holomorphic on `Re s > 1/2`. -/
def IsPairTwin (B : BeurlingSystem) (ρ : ℂ) : Prop :=
  ∃ (C : ℂ) (H : ℂ → ℂ), C ≠ 0 ∧ DifferentiableOn ℂ H {s : ℂ | 1 / 2 < s.re} ∧
    ∀ s : ℂ, 1 < s.re → (s - 1) * B.zetaSeriesC s =
      zetaResidueUnit s * (C * (s - ρ) * (s - (starRingEnd ℂ) ρ) * Complex.exp (H s))

/-- The fake zeros of `B` right of the line are exactly the points of `Z`: the continuation of
`(s − 1) ζ_B(s)` to `Re s > 1/2` vanishes, away from `1` and the zeros of `ζ`, exactly on `Z`. -/
def HasFakeZeroSet (B : BeurlingSystem) (Z : Set ℂ) : Prop :=
  ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re} ∧
    (∀ s : ℂ, 1 < s.re → G s = (s - 1) * B.zetaSeriesC s) ∧
    ∀ z : ℂ, 1 / 2 < z.re → z ≠ 1 → riemannZeta z ≠ 0 → (G z = 0 ↔ z ∈ Z)

theorem differentiable_zetaResidueUnit : Differentiable ℂ zetaResidueUnit :=
  fun s => (analyticAt_zetaResidueUnit s).differentiableAt

theorem zetaResidueUnit_of_ne {s : ℂ} (hs : s ≠ 1) :
    zetaResidueUnit s = (s - 1) * riemannZeta s := by
  simp [zetaResidueUnit, Function.update_of_ne hs]

/-- The continuation of `(s − 1) ζ_B(s)` of a pair twin. -/
theorem IsPairTwin.exists_continuation {B : BeurlingSystem} {ρ : ℂ} (h : IsPairTwin B ρ) :
    ∃ (C : ℂ) (H : ℂ → ℂ), C ≠ 0 ∧
      DifferentiableOn ℂ (fun s => zetaResidueUnit s *
        (C * (s - ρ) * (s - (starRingEnd ℂ) ρ) * Complex.exp (H s))) {s : ℂ | 1 / 2 < s.re} ∧
      ∀ s : ℂ, 1 < s.re → (s - 1) * B.zetaSeriesC s =
        zetaResidueUnit s * (C * (s - ρ) * (s - (starRingEnd ℂ) ρ) * Complex.exp (H s)) := by
  obtain ⟨C, H, hC, hH, hfac⟩ := h
  refine ⟨C, H, hC, differentiable_zetaResidueUnit.differentiableOn.mul ?_, hfac⟩
  exact (((differentiableOn_const C).mul (differentiableOn_id.sub_const ρ)).mul
    (differentiableOn_id.sub_const _)).mul hH.cexp

/-- The fake zeros of a pair twin right of the line are exactly `ρ` and `ρ̄`. -/
theorem IsPairTwin.hasFakeZeroSet {B : BeurlingSystem} {ρ : ℂ} (h : IsPairTwin B ρ) :
    HasFakeZeroSet B {ρ, (starRingEnd ℂ) ρ} := by
  obtain ⟨C, H, hC, hdiff, hfac⟩ := h.exists_continuation
  refine ⟨_, hdiff, fun s hs => (hfac s hs).symm, fun z _ hz1 hzζ => ?_⟩
  have hzu : zetaResidueUnit z ≠ 0 := by
    rw [zetaResidueUnit_of_ne hz1]
    exact mul_ne_zero (sub_ne_zero.mpr hz1) hzζ
  simp [hzu, hC, Complex.exp_ne_zero, sub_eq_zero]

/-- `(s − 1) ζ(s)` has no real zero right of the line. -/
theorem zetaResidueUnit_ofReal_ne_zero {x : ℝ} (hx : 1 / 2 < x) : zetaResidueUnit (x : ℂ) ≠ 0 := by
  rcases eq_or_ne x 1 with rfl | hx1
  · simp
  · have hne : (x : ℂ) ≠ 1 := by exact_mod_cast hx1
    rw [zetaResidueUnit_of_ne hne]
    refine mul_ne_zero (sub_ne_zero.mpr hne) ?_
    rcases lt_or_gt_of_ne hx1 with hlt | hgt
    · exact riemannZeta_ne_zero_of_abs_im_lt_four (by simp; linarith) (by simpa using hlt)
        (by simp)
    · exact riemannZeta_ne_zero_of_one_le_re (by simpa using hgt.le)

/-- **No real zero.**  The continuation of `(s − 1) ζ_B(s)` of a pair twin at a non-real `ρ` has no
real zero in `(1/2, ∞)`. -/
theorem IsPairTwin.ne_zero_of_real {B : BeurlingSystem} {ρ : ℂ} (h : IsPairTwin B ρ)
    (hρ : ρ.im ≠ 0) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re} ∧
      (∀ s : ℂ, 1 < s.re → G s = (s - 1) * B.zetaSeriesC s) ∧
      ∀ x : ℝ, 1 / 2 < x → G (x : ℂ) ≠ 0 := by
  obtain ⟨C, H, hC, hdiff, hfac⟩ := h.exists_continuation
  refine ⟨_, hdiff, fun s hs => (hfac s hs).symm, fun x hx => ?_⟩
  have h1 : (x : ℂ) - ρ ≠ 0 := fun h0 => hρ (by
    have h' := congrArg Complex.im h0
    simpa using h')
  have h2 : (x : ℂ) - (starRingEnd ℂ) ρ ≠ 0 := fun h0 => hρ (by
    have h' := congrArg Complex.im h0
    simpa using h')
  exact mul_ne_zero (zetaResidueUnit_ofReal_ne_zero hx)
    (mul_ne_zero (mul_ne_zero (mul_ne_zero hC h1) h2) (Complex.exp_ne_zero _))

theorem isEdit_edit (ρ : ℂ) : IsEdit (edit ρ) :=
  ⟨fun _ hk => edit_eq_zero_of_not_prime ρ hk, fun k => gedit_cases _ k⟩

/-- **The greedy edit at `ρ` is a pair twin of `ζ`**, for `1/2 < Re ρ < 14/15`. -/
theorem isPairTwin_editSystem {ρ : ℂ} (hρ : 1 / 2 < ρ.re) (hρ1 : ρ.re < 14 / 15) :
    IsPairTwin (editSystem (edit ρ)) ρ := by
  set α : ℝ := (17 / 30 + (3 / 2 - ρ.re)) / 2 with hα
  have hα0 : 17 / 30 < α := by rw [hα]; linarith
  have hα1 : α < 1 := by rw [hα]; linarith
  have hαc : α - (1 - ρ.re) ≤ 1 / 2 := by rw [hα]; linarith
  obtain ⟨X, -, hwin⟩ := RHTower.exists_theta_window_lower_seventeenThirtieths hα0 hα1
  obtain ⟨C, K, hC, hK, hfac⟩ := exists_exp_editSeries_eq (ρ := ρ) (c := 1 / 2) (by linarith)
    (by linarith) hα1 (by norm_num) (by norm_num) hαc hwin
  have he := isEdit_edit ρ
  refine ⟨C, fun s => K s + editRem (edit ρ) s, hC, hK.add (differentiableOn_editRem he),
    fun s hs => ?_⟩
  have hs1 : s ≠ 1 := fun h => by rw [h] at hs; norm_num at hs
  have hEK : Complex.exp (LSeries (fun k => (edit ρ k : ℂ)) s + editRem (edit ρ) s) =
      C * (s - ρ) * (s - (starRingEnd ℂ) ρ) * Complex.exp (K s + editRem (edit ρ) s) := by
    rw [Complex.exp_add, hfac s hs, Complex.exp_add]
    ring
  rw [editSystem_zetaSeriesC he hs, hEK, zetaResidueUnit_of_ne hs1]
  ring

/-- A pair twin of `ζ` at `ρ` with `Re ρ > 1/2` is not `ζ`: the greedy edit edits a prime. -/
theorem exists_edit_ne_zero {ρ : ℂ} (hρ : 1 / 2 < ρ.re) (hρ1 : ρ.re < 14 / 15)
    (hζ : riemannZeta ρ ≠ 0) : ∃ k, edit ρ k ≠ 0 := by
  by_contra hall
  push Not at hall
  have he := isEdit_edit ρ
  obtain ⟨C, H, hC, hdiff, hfac⟩ := (isPairTwin_editSystem hρ hρ1).exists_continuation
  -- with no edited prime the system is the rational primes
  have hz : ∀ s : ℂ, 1 < s.re →
      zetaResidueUnit s * (C * (s - ρ) * (s - (starRingEnd ℂ) ρ) * Complex.exp (H s)) =
        zetaResidueUnit s := by
    intro s hs
    have hs1 : s ≠ 1 := fun h => by rw [h] at hs; norm_num at hs
    have hfun : (fun k => (edit ρ k : ℂ)) = 0 := by
      funext k
      simp [hall k]
    have hL0 : LSeries (fun k => (edit ρ k : ℂ)) s = 0 := by
      rw [hfun]; simp
    have hR0 : editRem (edit ρ) s = 0 := by simp [editRem, hall]
    rw [← hfac s hs, editSystem_zetaSeriesC he hs, hL0, hR0, add_zero, Complex.exp_zero, mul_one,
      zetaResidueUnit_of_ne hs1]
  have hEq := eqOn_halfPlane_of_eq_on_one hdiff differentiable_zetaResidueUnit.differentiableOn hz
  have h0 := hEq (show ρ ∈ {s : ℂ | 1 / 2 < s.re} from hρ)
  have hρne : ρ ≠ 1 := fun h => by rw [h] at hρ1; norm_num at hρ1
  have hzu : zetaResidueUnit ρ ≠ 0 := by
    rw [zetaResidueUnit_of_ne hρne]
    exact mul_ne_zero (sub_ne_zero.mpr hρne) hζ
  simp only [sub_self, mul_zero, zero_mul] at h0
  exact hzu h0.symm

/-- **A non-real pair alone on top of a two-sided edit.**  For `1/2 < Re ρ < 14/15` with
`ζ(ρ) ≠ 0` and every `β ∈ (Re ρ, 1)` there is a two-sided edit of the rational primes that is an
integer-norm fake at `β` and a pair twin of `ζ` at `ρ`: its fake zeros right of the line are
exactly `ρ` and `ρ̄`. -/
theorem exists_isEdit_fake_with_zero_pair {ρ : ℂ} (hρ : 1 / 2 < ρ.re) (hρ1 : ρ.re < 14 / 15)
    (hζ : riemannZeta ρ ≠ 0) {β : ℝ} (hβ : ρ.re < β) (hβ1 : β < 1) :
    ∃ e : ℕ → ℤ, IsEdit e ∧ IsIntegerNormFakeAt (editSystem e) β ∧
      IsPairTwin (editSystem e) ρ ∧ HasFakeZeroSet (editSystem e) {ρ, (starRingEnd ℂ) ρ} := by
  have he := isEdit_edit ρ
  have htwin := isPairTwin_editSystem hρ hρ1
  obtain ⟨k, hk⟩ := exists_edit_ne_zero hρ hρ1 hζ
  obtain ⟨A, Cc, hA, hcount⟩ := editSystem_count (by linarith) hβ1
    (summable_abs_edit_rpow (by linarith) (by linarith) hβ)
  obtain ⟨C, H, hC, hdiff, hfac⟩ := htwin.exists_continuation
  have hρne : ρ ≠ 1 := fun h => by rw [h] at hρ1; norm_num at hρ1
  refine ⟨edit ρ, he, ⟨hasIntegerNorms_editSystem _, isDiscrete_editSystem _,
    notNormEquivPrimes_editSystem he hk, ⟨A, Cc, hA, hcount⟩, _, hdiff,
    fun s hs => (hfac s hs).symm, ρ, hρ, hρne, by simp, hζ⟩, htwin, htwin.hasFakeZeroSet⟩

/-- **A count rate does not force a real zero on top.**  For every `β > 1/2` there are a two-sided
edit of the rational primes and a non-real `ρ` with `Re ρ > 1/2` such that the system of the edit
is an integer-norm fake at `β` whose fake zeros right of the line are exactly `ρ` and `ρ̄`, and the
continuation of `(s − 1) ζ_B(s)` has no real zero in `(1/2, ∞)`. -/
theorem exists_isEdit_fake_without_real_zero {β : ℝ} (hβ : 1 / 2 < β) :
    ∃ (e : ℕ → ℤ) (ρ : ℂ), IsEdit e ∧ ρ.im ≠ 0 ∧ 1 / 2 < ρ.re ∧
      IsIntegerNormFakeAt (editSystem e) β ∧
      HasFakeZeroSet (editSystem e) {ρ, (starRingEnd ℂ) ρ} ∧
      ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re} ∧
        (∀ s : ℂ, 1 < s.re → G s = (s - 1) * (editSystem e).zetaSeriesC s) ∧
        ∀ x : ℝ, 1 / 2 < x → G (x : ℂ) ≠ 0 := by
  -- the exponent of the count, and the abscissa of the pair
  set β' : ℝ := min β (9 / 10) with hβ'
  have hβ'1 : 1 / 2 < β' := lt_min hβ (by norm_num)
  have hβ'2 : β' ≤ 9 / 10 := min_le_right _ _
  set ρ : ℂ := ⟨(1 / 2 + β') / 2, 1⟩ with hρdef
  have hre : ρ.re = (1 / 2 + β') / 2 := rfl
  have him : ρ.im = 1 := rfl
  have hρ : 1 / 2 < ρ.re := by rw [hre]; linarith
  have hρ1 : ρ.re < 14 / 15 := by rw [hre]; linarith
  have hζ : riemannZeta ρ ≠ 0 :=
    riemannZeta_ne_zero_of_abs_im_lt_four (by linarith) (by linarith) (by rw [him]; norm_num)
  obtain ⟨e, he, hfake, htwin, hset⟩ :=
    exists_isEdit_fake_with_zero_pair hρ hρ1 hζ (β := β') (by rw [hre]; linarith) (by linarith)
  exact ⟨e, ρ, he, by rw [him]; norm_num, hρ, hfake.mono (min_le_left _ _), hset,
    htwin.ne_zero_of_real (by rw [him]; norm_num)⟩

end GaloisForLFunctions.WorldsOfTheZeroConfiguration
