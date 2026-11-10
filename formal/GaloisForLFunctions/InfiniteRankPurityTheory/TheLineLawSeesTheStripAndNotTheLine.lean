import GaloisForLFunctions.InfiniteRankPurityTheory.TheEisensteinConstantTermIsPureByParity
import GaloisForLFunctions.RHTower.PerturbationZero
import GaloisForLFunctions.FiniteFreeProbability.HurwitzDeflation

/-!
# The line law sees the strip and not the line

What does a family prove about the object common to all its members? The cleared constant terms of
the Eisenstein series form the family

`F_Y(s) = (s − 1) G(2s) Y^s + s G(2s − 1) Y^{1−s}`,  `Y ≥ 1`,

with the fixed part `G = ξ` (`pencil`, `pencil_xi`). Every member satisfies the line law. This
module determines what that says about `G`.

* `pencil_indexOne`, `pencil_lineLaw`: for every real entire `G` with no zero in `Re w > 1`,
  `G(1) ≠ 0` and `‖G(w − 1)‖ ≤ ‖G(w)‖` on `Re w > 1`, every member has at most one zero right of the
  line and it is real. The position of the zeros of `G` inside the strip is not used.
* `norm_divisorPoly_sub_one_le`: the monic polynomial of a finite divisor in `Re ρ ≥ 0` that is
  symmetric under `ρ ↦ 1 − ρ̄` decreases under `w ↦ w − 1` on `Re w ≥ 1`: the factor at `ρ` is paired
  with the factor at `1 − ρ̄`.
* `exists_fixedPart_with_lineLaw`: every finite configuration of points of the closed strip other
  than `0` and `1` is contained in the zeros of a real polynomial with the functional equation whose
  family satisfies the line law for every `Y ≥ 1`. The fixed part may violate purity at any finite
  set of points while all members are pure off the real axis.
* `pencil_lineLaw_of_tendsto`, `xi_mem_pencil_class`: the same over every locally uniform limit of
  such polynomials, with no bound assumed on the limit; `ξ` satisfies the hypotheses of
  `pencil_indexOne`.
* `exists_nonreal_zero_pencil_of_zero_right`: conversely a non-real zero of `G` in `Re w > 1` forces
  a non-real zero right of the line in every member with `Y` large; as `Y → ∞` the member divided by
  `Y^s` tends to `(s − 1) G(2s)`.
* `divisorPencil_lineLaw_iff`: for a finite divisor without real points, symmetric under `ρ ↦ ρ̄`
  and `ρ ↦ 1 − ρ̄`, the line law for every `Y ≥ 1` holds exactly when the divisor lies in the closed
  strip.

So the family proves about its fixed part that its zeros lie in the closed strip, and nothing
about their position inside it.
-/

open Complex Filter Topology Set Metric

namespace GaloisForLFunctions.InfiniteRankPurityTheory

open _root_.RHTower GaloisForLFunctions.BlackHoleRingdown

noncomputable section

/-! ### The family over a fixed part -/

/-- `E(s) = G(2s) Y^s`. -/
def pencilHalf (G : ℂ → ℂ) (Y : ℝ) (s : ℂ) : ℂ := G (2 * s) * (Y : ℂ) ^ s

/-- `E'(s) = G(2s − 1) Y^{1−s}`. -/
def pencilDual (G : ℂ → ℂ) (Y : ℝ) (s : ℂ) : ℂ := G (2 * s - 1) * (Y : ℂ) ^ (1 - s)

/-- The member at `Y` of the family over the fixed part `G`:
`(s − 1) G(2s) Y^s + s G(2s − 1) Y^{1−s}`. -/
def pencil (G : ℂ → ℂ) (Y : ℝ) (s : ℂ) : ℂ := (s - 1) * pencilHalf G Y s + s * pencilDual G Y s

/-- Over `ξ` the family is the cleared constant term of the Eisenstein series. -/
theorem pencil_xi (Y : ℝ) (s : ℂ) : pencil xi Y s = constantTerm Y s := rfl

theorem two_mul_re_gt_one {s : ℂ} (hs : s ∈ rightHalf) : 1 < (2 * s).re := by
  have h1 : (1 : ℝ) / 2 < s.re := hs
  simp only [mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]
  linarith

theorem differentiable_pencilHalf {G : ℂ → ℂ} (hG : Differentiable ℂ G) {Y : ℝ} (hY : 0 < Y) :
    Differentiable ℂ (pencilHalf G Y) := by
  have hY0 : (Y : ℂ) ≠ 0 := by exact_mod_cast hY.ne'
  intro s
  have h1 : DifferentiableAt ℂ (fun s : ℂ => G (2 * s)) s := (hG (2 * s)).comp s (by fun_prop)
  have h2 : DifferentiableAt ℂ (fun s : ℂ => (Y : ℂ) ^ s) s :=
    differentiableAt_id.const_cpow (Or.inl hY0)
  exact h1.mul h2

theorem differentiable_pencilDual {G : ℂ → ℂ} (hG : Differentiable ℂ G) {Y : ℝ} (hY : 0 < Y) :
    Differentiable ℂ (pencilDual G Y) := by
  have hY0 : (Y : ℂ) ≠ 0 := by exact_mod_cast hY.ne'
  intro s
  have h1 : DifferentiableAt ℂ (fun s : ℂ => G (2 * s - 1)) s :=
    (hG (2 * s - 1)).comp s (by fun_prop)
  have h2 : DifferentiableAt ℂ (fun s : ℂ => (Y : ℂ) ^ (1 - s)) s :=
    ((differentiableAt_const _).sub differentiableAt_id).const_cpow (Or.inl hY0)
  exact h1.mul h2

theorem two_mul_conj (s : ℂ) : (2 : ℂ) * (starRingEnd ℂ) s = (starRingEnd ℂ) (2 * s) := by
  rw [map_mul, Complex.conj_ofNat]

theorem pencilHalf_ne_zero {G : ℂ → ℂ} (hne : ∀ w : ℂ, 1 < w.re → G w ≠ 0) {Y : ℝ}
    (hY : 0 < Y) {s : ℂ} (hs : s ∈ rightHalf) : pencilHalf G Y s ≠ 0 := by
  have hYc : (Y : ℂ) ≠ 0 := by exact_mod_cast hY.ne'
  exact mul_ne_zero (hne _ (two_mul_re_gt_one hs)) (Complex.cpow_ne_zero_iff.mpr (Or.inl hYc))

/-- The Schur bound of the family: `‖G(2s − 1) Y^{1−s}‖ ≤ ‖G(2s) Y^s‖` right of the line. -/
theorem norm_pencilDual_le {G : ℂ → ℂ} (hle : ∀ w : ℂ, 1 < w.re → ‖G (w - 1)‖ ≤ ‖G w‖)
    {Y : ℝ} (hY : 1 ≤ Y) {s : ℂ} (hs : s ∈ rightHalf) :
    ‖pencilDual G Y s‖ ≤ ‖pencilHalf G Y s‖ := by
  have hY0 : 0 < Y := by linarith
  have hs' : (1 : ℝ) / 2 < s.re := hs
  rw [pencilDual, pencilHalf, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hY0,
    Complex.norm_cpow_eq_rpow_re_of_pos hY0]
  have hpow : Y ^ (1 - s).re ≤ Y ^ s.re := by
    apply Real.rpow_le_rpow_of_exponent_le hY
    simp only [sub_re, one_re]
    linarith
  exact mul_le_mul (hle _ (two_mul_re_gt_one hs)) hpow (Real.rpow_nonneg hY0.le _)
    (norm_nonneg _)

/-- **A family over a fixed part with zeros left of `Re = 1` is of index one.** Let `G` be entire
and real, without zero in `Re w > 1`, with `G(1) ≠ 0` and `‖G(w − 1)‖ ≤ ‖G(w)‖` on `Re w > 1`. For
`Y ≥ 1` the member `F_Y` has at most one zero right of the line, and it is real. -/
theorem pencil_indexOne {G : ℂ → ℂ} (hG : Differentiable ℂ G)
    (hreal : ∀ s, G ((starRingEnd ℂ) s) = (starRingEnd ℂ) (G s))
    (hne : ∀ w : ℂ, 1 < w.re → G w ≠ 0) (hle : ∀ w : ℂ, 1 < w.re → ‖G (w - 1)‖ ≤ ‖G w‖)
    (h1 : G 1 ≠ 0) {Y : ℝ} (hY : 1 ≤ Y) :
    {s | s ∈ rightHalf ∧ pencil G Y s = 0}.Subsingleton ∧
      ∀ s ∈ rightHalf, pencil G Y s = 0 → s.im = 0 := by
  have hY0 : 0 < Y := by linarith
  have hYc : (Y : ℂ) ≠ 0 := by exact_mod_cast hY0.ne'
  have hEne : ∀ s ∈ rightHalf, pencilHalf G Y s ≠ 0 := fun s hs =>
    mul_ne_zero (hne _ (two_mul_re_gt_one hs)) (Complex.cpow_ne_zero_iff.mpr (Or.inl hYc))
  have hEle : ∀ s ∈ rightHalf, ‖pencilDual G Y s‖ ≤ ‖pencilHalf G Y s‖ := by
    intro s hs
    have hs' : (1 : ℝ) / 2 < s.re := hs
    rw [pencilDual, pencilHalf, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hY0,
      Complex.norm_cpow_eq_rpow_re_of_pos hY0]
    have hpow : Y ^ (1 - s).re ≤ Y ^ s.re := by
      apply Real.rpow_le_rpow_of_exponent_le hY
      simp only [sub_re, one_re]
      linarith
    exact mul_le_mul (hle _ (two_mul_re_gt_one hs)) hpow (Real.rpow_nonneg hY0.le _)
      (norm_nonneg _)
  have hEr : ∀ s ∈ rightHalf,
      pencilHalf G Y ((starRingEnd ℂ) s) = (starRingEnd ℂ) (pencilHalf G Y s) := by
    intro s _
    rw [pencilHalf, pencilHalf, map_mul, two_mul_conj, hreal, cpow_conj_of_pos hY0]
  have hE'r : ∀ s ∈ rightHalf,
      pencilDual G Y ((starRingEnd ℂ) s) = (starRingEnd ℂ) (pencilDual G Y s) := by
    intro s _
    have a : (2 : ℂ) * (starRingEnd ℂ) s - 1 = (starRingEnd ℂ) (2 * s - 1) := by
      rw [map_sub, map_one, two_mul_conj]
    have b : (1 : ℂ) - (starRingEnd ℂ) s = (starRingEnd ℂ) (1 - s) := by rw [map_sub, map_one]
    rw [pencilDual, pencilDual, map_mul, a, hreal, b, cpow_conj_of_pos hY0]
  have hform : ∀ s : ℂ, pencil G Y s =
      (s - 1) * pencilHalf G Y s - (-1 : ℂ) * (s - (1 - 1)) * pencilDual G Y s := by
    intro s
    rw [pencil]
    ring
  have hval : pencil G Y 1 = G 1 := by
    rw [pencil, pencilDual]
    norm_num
  have hdiff : ∃ z ∈ rightHalf,
      (z - 1) * pencilHalf G Y z - (-1 : ℂ) * (z - (1 - 1)) * pencilDual G Y z ≠ 0 := by
    refine ⟨1, one_mem_rightHalf, ?_⟩
    rw [← hform, hval]
    exact h1
  have h := hermiteBiehler_indexOne (E := pencilHalf G Y) (E' := pencilDual G Y) (w := 1)
    (c := -1) (differentiable_pencilHalf hG hY0).differentiableOn
    (differentiable_pencilDual hG hY0).differentiableOn hEne hEle hEr hE'r one_mem_rightHalf
    (map_one _) (by simp) (by simp) hdiff
  simp only [← hform] at h
  exact h

/-- A functional equation `G(1 − s) = ε G(s)` reflects the family: `F_Y(1 − s) = −ε F_Y(s)`. -/
theorem pencil_one_sub {G : ℂ → ℂ} {ε : ℂ} (hfe : ∀ s, G (1 - s) = ε * G s) (Y : ℝ) (s : ℂ) :
    pencil G Y (1 - s) = -ε * pencil G Y s := by
  have a : G (2 * (1 - s)) = ε * G (2 * s - 1) := by
    rw [← hfe]
    congr 1
    ring
  have b : G (2 * (1 - s) - 1) = ε * G (2 * s) := by
    rw [← hfe]
    congr 1
    ring
  rw [pencil, pencil, pencilHalf, pencilDual, pencilHalf, pencilDual, a, b, sub_sub_cancel]
  ring

/-- **The line law over any such fixed part.** With a functional equation `G(1 − s) = ε G(s)`,
every zero of a member `Y ≥ 1` off the line `Re s = ½` is real. -/
theorem pencil_lineLaw {G : ℂ → ℂ} (hG : Differentiable ℂ G)
    (hreal : ∀ s, G ((starRingEnd ℂ) s) = (starRingEnd ℂ) (G s)) {ε : ℂ}
    (hfe : ∀ s, G (1 - s) = ε * G s) (hne : ∀ w : ℂ, 1 < w.re → G w ≠ 0)
    (hle : ∀ w : ℂ, 1 < w.re → ‖G (w - 1)‖ ≤ ‖G w‖) (h1 : G 1 ≠ 0) {Y : ℝ} (hY : 1 ≤ Y)
    {s : ℂ} (hre : s.re ≠ 1 / 2) (h : pencil G Y s = 0) : s.im = 0 := by
  have hidx := pencil_indexOne hG hreal hne hle h1 hY
  rcases lt_or_gt_of_ne hre with hlt | hgt
  · have hmem : 1 - s ∈ rightHalf := by
      show (1 : ℝ) / 2 < (1 - s).re
      simp only [sub_re, one_re]
      linarith
    have h0 : pencil G Y (1 - s) = 0 := by rw [pencil_one_sub hfe, h, mul_zero]
    have := hidx.2 (1 - s) hmem h0
    simpa using this
  · exact hidx.2 s hgt h

/-! ### Finite divisors in the closed strip -/

/-- The monic polynomial with the zeros `Z`. -/
def divisorPoly (Z : Multiset ℂ) (s : ℂ) : ℂ := (Z.map fun ρ => s - ρ).prod

theorem divisorPoly_zero (s : ℂ) : divisorPoly 0 s = 1 := by simp [divisorPoly]

theorem divisorPoly_cons (a : ℂ) (Z : Multiset ℂ) (s : ℂ) :
    divisorPoly (a ::ₘ Z) s = (s - a) * divisorPoly Z s := by simp [divisorPoly]

theorem differentiable_divisorPoly (Z : Multiset ℂ) : Differentiable ℂ (divisorPoly Z) := by
  induction Z using Multiset.induction_on with
  | empty =>
    rw [show divisorPoly 0 = fun _ => (1 : ℂ) from funext divisorPoly_zero]
    exact differentiable_const _
  | cons a Z ih =>
    rw [show divisorPoly (a ::ₘ Z) = fun s => (s - a) * divisorPoly Z s from
      funext (divisorPoly_cons a Z)]
    exact (differentiable_id.sub (differentiable_const _)).mul ih

theorem divisorPoly_eq_zero_iff {Z : Multiset ℂ} {s : ℂ} : divisorPoly Z s = 0 ↔ s ∈ Z := by
  rw [divisorPoly, Multiset.prod_eq_zero_iff, Multiset.mem_map]
  constructor
  · rintro ⟨ρ, hρ, h⟩
    rwa [sub_eq_zero.mp h]
  · intro h
    exact ⟨s, h, sub_self s⟩

theorem norm_divisorPoly (Z : Multiset ℂ) (s : ℂ) :
    ‖divisorPoly Z s‖ = (Z.map fun ρ => ‖s - ρ‖).prod := by
  induction Z using Multiset.induction_on with
  | empty => simp [divisorPoly]
  | cons a Z ih => rw [divisorPoly_cons, norm_mul, ih, Multiset.map_cons, Multiset.prod_cons]

/-- A divisor symmetric under conjugation has a real polynomial. -/
theorem divisorPoly_conj {Z : Multiset ℂ} (hconj : Z.map (starRingEnd ℂ) = Z) (s : ℂ) :
    divisorPoly Z ((starRingEnd ℂ) s) = (starRingEnd ℂ) (divisorPoly Z s) := by
  have h1 : divisorPoly Z ((starRingEnd ℂ) s) =
      (Z.map fun ρ => (starRingEnd ℂ) s - (starRingEnd ℂ) ρ).prod := by
    conv_lhs => rw [← hconj]
    rw [divisorPoly, Multiset.map_map]
    rfl
  rw [h1, divisorPoly, map_multiset_prod, Multiset.map_map]
  congr 1
  exact Multiset.map_congr rfl fun ρ _ => by simp

/-- A divisor symmetric under `ρ ↦ 1 − ρ` has a polynomial with a functional equation. -/
theorem divisorPoly_one_sub {Z : Multiset ℂ} (hfe : Z.map (fun ρ => 1 - ρ) = Z) (s : ℂ) :
    divisorPoly Z (1 - s) = (-1) ^ Multiset.card Z * divisorPoly Z s := by
  have h1 : divisorPoly Z s = (Z.map fun ρ => s - (1 - ρ)).prod := by
    conv_lhs => rw [← hfe]
    rw [divisorPoly, Multiset.map_map]
    rfl
  have h2 : (Z.map fun ρ => 1 - s - ρ) = (Z.map fun ρ => s - (1 - ρ)).map Neg.neg := by
    rw [Multiset.map_map]
    exact Multiset.map_congr rfl fun ρ _ => by
      simp only [Function.comp_apply]
      ring
  rw [divisorPoly, h2, Multiset.prod_map_neg, Multiset.card_map, ← h1]

/-- The factor at `ρ` is dominated by the factor at `1 − ρ̄` after the shift `w ↦ w − 1`. -/
theorem norm_sub_one_sub_le {w ρ : ℂ} (hw : 1 ≤ w.re) (hρ : 0 ≤ ρ.re) :
    ‖w - 1 - ρ‖ ≤ ‖w - (1 - (starRingEnd ℂ) ρ)‖ := by
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.normSq_apply]
  simp only [sub_re, sub_im, one_re, one_im, conj_re, conj_im]
  nlinarith [mul_nonneg hρ (sub_nonneg.mpr hw)]

/-- **The reflection bound for a finite divisor.** If `Z` lies in `Re ρ ≥ 0` and is symmetric under
`ρ ↦ 1 − ρ̄`, then `‖G_Z(w − 1)‖ ≤ ‖G_Z(w)‖` for `Re w ≥ 1`. -/
theorem norm_divisorPoly_sub_one_le {Z : Multiset ℂ}
    (hsymm : Z.map (fun ρ => 1 - (starRingEnd ℂ) ρ) = Z) (hstrip : ∀ ρ ∈ Z, 0 ≤ ρ.re) {w : ℂ}
    (hw : 1 ≤ w.re) : ‖divisorPoly Z (w - 1)‖ ≤ ‖divisorPoly Z w‖ := by
  have h1 : ‖divisorPoly Z w‖ = (Z.map fun ρ => ‖w - (1 - (starRingEnd ℂ) ρ)‖).prod := by
    conv_lhs => rw [← hsymm]
    rw [norm_divisorPoly, Multiset.map_map]
    rfl
  rw [norm_divisorPoly, h1]
  exact Multiset.prod_map_le_prod_map₀ _ _ (fun ρ _ => norm_nonneg _)
    fun ρ hρ => norm_sub_one_sub_le hw (hstrip ρ hρ)

theorem re_le_one_of_symm {Z : Multiset ℂ} (hsymm : Z.map (fun ρ => 1 - (starRingEnd ℂ) ρ) = Z)
    (hstrip : ∀ ρ ∈ Z, 0 ≤ ρ.re) {ρ : ℂ} (hρ : ρ ∈ Z) : ρ.re ≤ 1 := by
  rw [← hsymm, Multiset.mem_map] at hρ
  obtain ⟨ρ', hρ', rfl⟩ := hρ
  have := hstrip ρ' hρ'
  simp only [sub_re, one_re, conj_re]
  linarith

theorem map_one_sub_of_symm {Z : Multiset ℂ} (hconj : Z.map (starRingEnd ℂ) = Z)
    (hsymm : Z.map (fun ρ => 1 - (starRingEnd ℂ) ρ) = Z) : Z.map (fun ρ => 1 - ρ) = Z := by
  have h : Z.map (fun ρ => 1 - ρ) = (Z.map (starRingEnd ℂ)).map fun ρ => 1 - (starRingEnd ℂ) ρ := by
    rw [Multiset.map_map]
    exact Multiset.map_congr rfl fun ρ _ => by simp
  rw [h, hconj, hsymm]

/-- **The family over a finite divisor in the closed strip is of index one.** -/
theorem divisorPencil_indexOne {Z : Multiset ℂ} (hconj : Z.map (starRingEnd ℂ) = Z)
    (hsymm : Z.map (fun ρ => 1 - (starRingEnd ℂ) ρ) = Z) (hstrip : ∀ ρ ∈ Z, 0 ≤ ρ.re)
    (h1 : (1 : ℂ) ∉ Z) {Y : ℝ} (hY : 1 ≤ Y) :
    {s | s ∈ rightHalf ∧ pencil (divisorPoly Z) Y s = 0}.Subsingleton ∧
      ∀ s ∈ rightHalf, pencil (divisorPoly Z) Y s = 0 → s.im = 0 :=
  pencil_indexOne (differentiable_divisorPoly Z) (divisorPoly_conj hconj)
    (fun w hw h0 => by
      have := re_le_one_of_symm hsymm hstrip (divisorPoly_eq_zero_iff.mp h0)
      linarith)
    (fun w hw => norm_divisorPoly_sub_one_le hsymm hstrip hw.le)
    (fun h0 => h1 (divisorPoly_eq_zero_iff.mp h0)) hY

/-- **The line law over a finite divisor in the closed strip.** -/
theorem divisorPencil_lineLaw {Z : Multiset ℂ} (hconj : Z.map (starRingEnd ℂ) = Z)
    (hsymm : Z.map (fun ρ => 1 - (starRingEnd ℂ) ρ) = Z) (hstrip : ∀ ρ ∈ Z, 0 ≤ ρ.re)
    (h1 : (1 : ℂ) ∉ Z) {Y : ℝ} (hY : 1 ≤ Y) {s : ℂ} (hre : s.re ≠ 1 / 2)
    (h : pencil (divisorPoly Z) Y s = 0) : s.im = 0 :=
  pencil_lineLaw (differentiable_divisorPoly Z) (divisorPoly_conj hconj)
    (divisorPoly_one_sub (map_one_sub_of_symm hconj hsymm))
    (fun w hw h0 => by
      have := re_le_one_of_symm hsymm hstrip (divisorPoly_eq_zero_iff.mp h0)
      linarith)
    (fun w hw => norm_divisorPoly_sub_one_le hsymm hstrip hw.le)
    (fun h0 => h1 (divisorPoly_eq_zero_iff.mp h0)) hY hre h

/-! ### Every finite configuration in the strip is a fixed part -/

/-- The smallest divisor containing `M` that is symmetric under `ρ ↦ ρ̄` and `ρ ↦ 1 − ρ̄`. -/
def symmetrize (M : Multiset ℂ) : Multiset ℂ :=
  M + M.map (starRingEnd ℂ) + M.map (fun ρ => 1 - (starRingEnd ℂ) ρ) + M.map (fun ρ => 1 - ρ)

theorem mem_symmetrize {M : Multiset ℂ} {z : ℂ} : z ∈ symmetrize M ↔
    ∃ ρ ∈ M, z = ρ ∨ z = (starRingEnd ℂ) ρ ∨ z = 1 - (starRingEnd ℂ) ρ ∨ z = 1 - ρ := by
  simp only [symmetrize, Multiset.mem_add, Multiset.mem_map]
  constructor
  · rintro (((h | ⟨ρ, hρ, rfl⟩) | ⟨ρ, hρ, rfl⟩) | ⟨ρ, hρ, rfl⟩)
    · exact ⟨z, h, Or.inl rfl⟩
    · exact ⟨ρ, hρ, Or.inr (Or.inl rfl)⟩
    · exact ⟨ρ, hρ, Or.inr (Or.inr (Or.inl rfl))⟩
    · exact ⟨ρ, hρ, Or.inr (Or.inr (Or.inr rfl))⟩
  · rintro ⟨ρ, hρ, rfl | rfl | rfl | rfl⟩
    · exact Or.inl (Or.inl (Or.inl hρ))
    · exact Or.inl (Or.inl (Or.inr ⟨ρ, hρ, rfl⟩))
    · exact Or.inl (Or.inr ⟨ρ, hρ, rfl⟩)
    · exact Or.inr ⟨ρ, hρ, rfl⟩

theorem map_conj_map_conj (M : Multiset ℂ) :
    (M.map (starRingEnd ℂ)).map (starRingEnd ℂ) = M := by
  rw [Multiset.map_map]
  exact (Multiset.map_congr rfl fun ρ _ => Complex.conj_conj ρ).trans (Multiset.map_id' M)

theorem symmetrize_map_conj (M : Multiset ℂ) :
    (symmetrize M).map (starRingEnd ℂ) = symmetrize M := by
  have e2 : (M.map fun ρ => 1 - (starRingEnd ℂ) ρ).map (starRingEnd ℂ) = M.map fun ρ => 1 - ρ := by
    rw [Multiset.map_map]
    exact Multiset.map_congr rfl fun ρ _ => by simp
  have e3 : (M.map fun ρ => 1 - ρ).map (starRingEnd ℂ) =
      M.map fun ρ => 1 - (starRingEnd ℂ) ρ := by
    rw [Multiset.map_map]
    exact Multiset.map_congr rfl fun ρ _ => by simp
  rw [symmetrize, Multiset.map_add, Multiset.map_add, Multiset.map_add, map_conj_map_conj, e2, e3]
  abel

theorem symmetrize_map_symm (M : Multiset ℂ) :
    (symmetrize M).map (fun ρ => 1 - (starRingEnd ℂ) ρ) = symmetrize M := by
  have e1 : (M.map (starRingEnd ℂ)).map (fun ρ => 1 - (starRingEnd ℂ) ρ) = M.map fun ρ => 1 - ρ := by
    rw [Multiset.map_map]
    exact Multiset.map_congr rfl fun ρ _ => by simp
  have e2 : (M.map fun ρ => 1 - (starRingEnd ℂ) ρ).map (fun ρ => 1 - (starRingEnd ℂ) ρ) = M := by
    rw [Multiset.map_map]
    exact (Multiset.map_congr rfl fun ρ _ => by simp).trans (Multiset.map_id' M)
  have e3 : (M.map fun ρ => 1 - ρ).map (fun ρ => 1 - (starRingEnd ℂ) ρ) =
      M.map (starRingEnd ℂ) := by
    rw [Multiset.map_map]
    exact Multiset.map_congr rfl fun ρ _ => by simp
  rw [symmetrize, Multiset.map_add, Multiset.map_add, Multiset.map_add, e1, e2, e3]
  abel

theorem card_symmetrize (M : Multiset ℂ) :
    Multiset.card (symmetrize M) = 2 * (2 * Multiset.card M) := by
  simp only [symmetrize, Multiset.card_add, Multiset.card_map]
  ring

/-- **The line law is blind to the strip.** Every finite configuration `M` of points of the closed
strip other than `0` and `1` lies in the zero set of a real polynomial `G` with `G(1 − s) = G(s)`
whose family satisfies the line law for every `Y ≥ 1`. -/
theorem exists_fixedPart_with_lineLaw (M : Multiset ℂ)
    (hM : ∀ ρ ∈ M, 0 ≤ ρ.re ∧ ρ.re ≤ 1 ∧ ρ ≠ 0 ∧ ρ ≠ 1) :
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ (∀ s, G ((starRingEnd ℂ) s) = (starRingEnd ℂ) (G s)) ∧
      (∀ s, G (1 - s) = G s) ∧ (∀ ρ ∈ M, G ρ = 0) ∧
      ∀ Y : ℝ, 1 ≤ Y → ∀ s : ℂ, s.re ≠ 1 / 2 → pencil G Y s = 0 → s.im = 0 := by
  have hconj := symmetrize_map_conj M
  have hsymm := symmetrize_map_symm M
  have hstrip : ∀ ρ ∈ symmetrize M, 0 ≤ ρ.re := by
    intro z hz
    obtain ⟨ρ, hρ, h | h | h | h⟩ := mem_symmetrize.mp hz
    · rw [h]
      exact (hM ρ hρ).1
    · rw [h, conj_re]
      exact (hM ρ hρ).1
    · rw [h]
      simp only [sub_re, one_re, conj_re]
      linarith [(hM ρ hρ).2.1]
    · rw [h]
      simp only [sub_re, one_re]
      linarith [(hM ρ hρ).2.1]
  have h1 : (1 : ℂ) ∉ symmetrize M := by
    intro hz
    obtain ⟨ρ, hρ, h | h | h | h⟩ := mem_symmetrize.mp hz
    · exact (hM ρ hρ).2.2.2 h.symm
    · apply (hM ρ hρ).2.2.2
      have := congrArg (starRingEnd ℂ) h
      simpa using this.symm
    · apply (hM ρ hρ).2.2.1
      have h' : (starRingEnd ℂ) ρ = 0 := by linear_combination h
      simpa using h'
    · apply (hM ρ hρ).2.2.1
      linear_combination h
  have hfe : ∀ s, divisorPoly (symmetrize M) (1 - s) = divisorPoly (symmetrize M) s := by
    intro s
    rw [divisorPoly_one_sub (map_one_sub_of_symm hconj hsymm), card_symmetrize,
      Even.neg_one_pow ⟨2 * Multiset.card M, by ring⟩, one_mul]
  exact ⟨divisorPoly (symmetrize M), differentiable_divisorPoly _, divisorPoly_conj hconj, hfe,
    fun ρ hρ => divisorPoly_eq_zero_iff.mpr (mem_symmetrize.mpr ⟨ρ, hρ, Or.inl rfl⟩),
    fun Y hY s hre h => divisorPencil_lineLaw hconj hsymm hstrip h1 hY hre h⟩

/-! ### Limits of finite divisors -/

/-- **The line law over limits of finite divisors.** Let `G` be real entire with a functional
equation and `G(1) ≠ 0`, a locally uniform limit of constant multiples of the polynomials of finite
divisors `Z_n` in `Re ρ ≥ 0` symmetric under `ρ ↦ 1 − ρ̄`. Then every member `Y ≥ 1` of the family
over `G` satisfies the line law. No bound on `G` is assumed: the reflection bound passes to the
limit pointwise and the zero-free half-plane by Hurwitz. -/
theorem pencil_lineLaw_of_tendsto {G : ℂ → ℂ} (hG : Differentiable ℂ G)
    (hreal : ∀ s, G ((starRingEnd ℂ) s) = (starRingEnd ℂ) (G s)) {ε : ℂ}
    (hfe : ∀ s, G (1 - s) = ε * G s) (h1 : G 1 ≠ 0) {Z : ℕ → Multiset ℂ} {a : ℕ → ℂ}
    (hsymm : ∀ n, (Z n).map (fun ρ => 1 - (starRingEnd ℂ) ρ) = Z n)
    (hstrip : ∀ n, ∀ ρ ∈ Z n, 0 ≤ ρ.re)
    (hlim : TendstoLocallyUniformly (fun n s => a n * divisorPoly (Z n) s) G atTop) {Y : ℝ}
    (hY : 1 ≤ Y) {s : ℂ} (hre : s.re ≠ 1 / 2) (h : pencil G Y s = 0) : s.im = 0 := by
  have hpt : ∀ w : ℂ, Tendsto (fun n => a n * divisorPoly (Z n) w) atTop (𝓝 (G w)) := fun w =>
    (tendstoLocallyUniformlyOn_univ.mpr hlim).tendsto_at (Set.mem_univ w)
  have hle : ∀ w : ℂ, 1 < w.re → ‖G (w - 1)‖ ≤ ‖G w‖ := by
    intro w hw
    refine le_of_tendsto_of_tendsto' (hpt (w - 1)).norm (hpt w).norm fun n => ?_
    rw [norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_divisorPoly_sub_one_le (hsymm n) (hstrip n) hw.le)
      (norm_nonneg _)
  have hne : ∀ w : ℂ, 1 < w.re → G w ≠ 0 := by
    intro w hw h0
    have ha : ∀ᶠ n in atTop, a n ≠ 0 := by
      filter_upwards [(hpt 1).eventually_ne h1] with n hn h0'
      exact hn (by rw [h0', zero_mul])
    have hz := FiniteFreeProbability.eventually_exists_zero_of_tendstoLocallyUniformly hlim
      (fun n => (differentiable_divisorPoly (Z n)).const_mul (a n)) hG h1 h0
      (r := (w.re - 1) / 2) (by linarith)
    obtain ⟨n, hn, u, hu, hzero⟩ := (ha.and hz).exists
    have huZ : u ∈ Z n := divisorPoly_eq_zero_iff.mp ((mul_eq_zero.mp hzero).resolve_left hn)
    have hure : u.re ≤ 1 := re_le_one_of_symm (hsymm n) (hstrip n) huZ
    have hdist : ‖u - w‖ < (w.re - 1) / 2 := by
      rw [← dist_eq_norm]
      exact mem_ball.mp hu
    have habs : |(u - w).re| ≤ ‖u - w‖ := Complex.abs_re_le_norm _
    have hlow := (abs_le.mp (habs.trans hdist.le)).1
    simp only [sub_re] at hlow
    linarith
  exact pencil_lineLaw hG hreal hfe hne hle h1 hY hre h

/-- `ξ` satisfies the hypotheses of `pencil_indexOne`: the line law of the Eisenstein constant term
is the member `G = ξ` of the class. -/
theorem xi_mem_pencil_class : (∀ w : ℂ, 1 < w.re → xi w ≠ 0) ∧
    (∀ w : ℂ, 1 < w.re → ‖xi (w - 1)‖ ≤ ‖xi w‖) ∧ xi 1 ≠ 0 := by
  refine ⟨fun w hw => xi_ne_zero_of_one_le_re hw.le, fun w hw => ?_, ?_⟩
  · have h0 : 0 ≤ ((w - 1) / 2).re := by
      simp only [div_re, sub_re, one_re, re_ofNat, sub_im, one_im, im_ofNat, mul_zero, zero_div,
        add_zero, normSq_ofNat]
      have : 0 ≤ w.re - 1 := by linarith
      positivity
    have hxi := norm_xi_two_mul_le h0
    rwa [show 2 * ((w - 1) / 2) = w - 1 by ring, show 1 + (w - 1) = w by ring] at hxi
  · rw [xi_one]
    norm_num

/-! ### A zero right of `Re = 1` is seen -/

/-- **A zero of the fixed part right of `Re = 1` is seen by the family.** If the entire function
`G ≢ 0` has a non-real zero `w₀` with `Re w₀ > 1`, every member with `Y` large has a non-real zero
right of the line: `F_Y(s) Y^{−s} = (s − 1) G(2s) + s G(2s − 1) Y^{1−2s}` and the second term tends
to zero uniformly near `w₀/2`. -/
theorem exists_nonreal_zero_pencil_of_zero_right {G : ℂ → ℂ} (hG : Differentiable ℂ G) {a : ℂ}
    (ha : G a ≠ 0) {w₀ : ℂ} (hw₀ : G w₀ = 0) (hre : 1 < w₀.re) (him : w₀.im ≠ 0) :
    ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y → ∃ s ∈ rightHalf, s.im ≠ 0 ∧ pencil G Y s = 0 := by
  obtain ⟨s₀, hs₀⟩ : ∃ s₀ : ℂ, s₀ = w₀ / 2 := ⟨_, rfl⟩
  have h2s₀ : 2 * s₀ = w₀ := by rw [hs₀, mul_div_cancel₀ _ (two_ne_zero)]
  have hs₀re : (1 : ℝ) / 2 < s₀.re := by
    have : s₀.re = w₀.re / 2 := by rw [hs₀]; simp
    linarith
  have hs₀im : s₀.im ≠ 0 := by
    have : s₀.im = w₀.im / 2 := by rw [hs₀]; simp
    rw [this]
    exact div_ne_zero him two_ne_zero
  -- the zero of `s ↦ G(2s)` at `s₀` is isolated
  have hkd : Differentiable ℂ fun s : ℂ => G (2 * s) := fun s => (hG (2 * s)).comp s (by fun_prop)
  have hpunct : ∀ᶠ s in 𝓝[≠] s₀, G (2 * s) ≠ 0 := by
    refine (hkd.analyticAt s₀).eventually_eq_zero_or_eventually_ne_zero.resolve_left fun hev => ?_
    have han : AnalyticOnNhd ℂ (fun s : ℂ => G (2 * s)) univ := fun z _ => hkd.analyticAt z
    have hall := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (mem_univ s₀) hev (mem_univ (a / 2))
    apply ha
    have h2a : 2 * (a / 2) = a := mul_div_cancel₀ _ two_ne_zero
    simpa [h2a] using hall
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhdsWithin_iff.mp hpunct
  -- a radius keeping the ball right of the line and off the real axis
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = (s₀.re - 1 / 2) / 2 := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη]; linarith
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = min (δ / 2) (min η (|s₀.im| / 2)) := ⟨_, rfl⟩
  have hr0 : 0 < r := by
    rw [hr]
    exact lt_min (half_pos hδ) (lt_min hη0 (half_pos (abs_pos.mpr hs₀im)))
  have hrδ : r < δ := by
    rw [hr]
    exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hδ)
  have hrη : r ≤ η := by
    rw [hr]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hrim : r ≤ |s₀.im| / 2 := by
    rw [hr]
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hball_re : ∀ z ∈ closedBall s₀ r, 1 / 2 + η ≤ z.re := by
    intro z hz
    have h1 : |(z - s₀).re| ≤ ‖z - s₀‖ := Complex.abs_re_le_norm _
    have h2 : ‖z - s₀‖ ≤ r := by simpa [dist_eq_norm] using mem_closedBall.mp hz
    have h3 := (abs_le.mp (h1.trans h2)).1
    simp only [sub_re] at h3
    rw [hη] at hrη ⊢
    linarith
  have hball_im : ∀ z ∈ closedBall s₀ r, z.im ≠ 0 := by
    intro z hz him0
    have h1 : |(z - s₀).im| ≤ ‖z - s₀‖ := Complex.abs_im_le_norm _
    have h2 : ‖z - s₀‖ ≤ r := by simpa [dist_eq_norm] using mem_closedBall.mp hz
    have h3 := h1.trans h2
    simp only [sub_im, him0, zero_sub, abs_neg] at h3
    have : 0 < |s₀.im| := abs_pos.mpr hs₀im
    linarith
  -- the limit `h(s) = (s − 1) G(2s)` vanishes at `s₀` and not on the sphere
  have hhd : Differentiable ℂ fun s : ℂ => (s - 1) * G (2 * s) :=
    (differentiable_id.sub (differentiable_const _)).mul hkd
  have hh0 : (s₀ - 1) * G (2 * s₀) = 0 := by rw [h2s₀, hw₀, mul_zero]
  have hsphere : ∀ z ∈ sphere s₀ r, (z - 1) * G (2 * z) ≠ 0 := by
    intro z hz
    have hzb : z ∈ closedBall s₀ r := sphere_subset_closedBall hz
    refine mul_ne_zero (fun h1 => hball_im z hzb ?_)
      (hδsub ⟨mem_ball.mpr ((mem_sphere.mp hz).trans_lt hrδ), ne_of_mem_sphere hz hr0.ne'⟩)
    rw [sub_eq_zero.mp h1]
    simp
  obtain ⟨z₁, hz₁, hmin⟩ := (isCompact_sphere s₀ r).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hr0.le) hhd.continuous.continuousOn.norm
  have hpos : 0 < ‖(z₁ - 1) * G (2 * z₁)‖ := norm_pos_iff.mpr (hsphere z₁ hz₁)
  -- the reflected coefficient is bounded on the ball
  have hcd : Differentiable ℂ fun s : ℂ => s * G (2 * s - 1) :=
    differentiable_id.mul fun s => (hG (2 * s - 1)).comp s (by fun_prop)
  obtain ⟨M, hM⟩ := (isCompact_closedBall s₀ r).exists_bound_of_continuousOn
    hcd.continuous.continuousOn
  have htend : Tendsto (fun Y : ℝ => 3 * (|M| * Y ^ (-(2 * η)))) atTop (𝓝 0) := by
    have := ((tendsto_rpow_neg_atTop (by linarith : 0 < 2 * η)).const_mul |M|).const_mul 3
    simpa using this
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.mp
    ((htend.eventually (gt_mem_nhds hpos)).and (eventually_ge_atTop (1 : ℝ)))
  refine ⟨Y₀, fun Y hY => ?_⟩
  obtain ⟨hsmall, hY1⟩ := hY₀ Y hY
  have hYpos : 0 < Y := by linarith
  have hYc : (Y : ℂ) ≠ 0 := by exact_mod_cast hYpos.ne'
  have hgd : Differentiable ℂ fun s : ℂ => s * G (2 * s - 1) * (Y : ℂ) ^ (1 - 2 * s) :=
    hcd.mul fun s => ((differentiableAt_const _).sub
      ((differentiableAt_const _).mul differentiableAt_id)).const_cpow (Or.inl hYc)
  have hpen : ∀ z : ℂ, pencil G Y z =
      (Y : ℂ) ^ z * (z * G (2 * z - 1) * (Y : ℂ) ^ (1 - 2 * z) + (z - 1) * G (2 * z)) := by
    intro z
    have hsplit : (Y : ℂ) ^ (1 - z) = (Y : ℂ) ^ z * (Y : ℂ) ^ (1 - 2 * z) := by
      rw [← Complex.cpow_add _ _ hYc]
      congr 1
      ring
    rw [pencil, pencilHalf, pencilDual, hsplit]
    ring
  have hgb : ∀ z ∈ closedBall s₀ r,
      ‖z * G (2 * z - 1) * (Y : ℂ) ^ (1 - 2 * z)‖ ≤ |M| * Y ^ (-(2 * η)) := by
    intro z hz
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hYpos]
    have hexp : (1 - 2 * z).re ≤ -(2 * η) := by
      have := hball_re z hz
      simp only [sub_re, one_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]
      linarith
    exact mul_le_mul ((hM z hz).trans (le_abs_self M))
      (Real.rpow_le_rpow_of_exponent_le hY1 hexp) (Real.rpow_nonneg hYpos.le _) (abs_nonneg M)
  have hzero : ∃ z ∈ closedBall s₀ r,
      z * G (2 * z - 1) * (Y : ℂ) ^ (1 - 2 * z) + (z - 1) * G (2 * z) = 0 := by
    by_cases hg0 : s₀ * G (2 * s₀ - 1) * (Y : ℂ) ^ (1 - 2 * s₀) = 0
    · exact ⟨s₀, mem_closedBall_self hr0.le, by rw [hg0, hh0, add_zero]⟩
    · refine exists_zero_of_sphere_domination hr0 hgd.diffContOnCl hhd.diffContOnCl hh0 hg0
        fun z hz => ?_
      have hminz : ‖(z₁ - 1) * G (2 * z₁)‖ ≤ ‖(z - 1) * G (2 * z)‖ := hmin hz
      linarith [hgb z (sphere_subset_closedBall hz)]
  obtain ⟨z, hzb, hz0⟩ := hzero
  refine ⟨z, ?_, hball_im z hzb, by rw [hpen, hz0, mul_zero]⟩
  show (1 : ℝ) / 2 < z.re
  linarith [hball_re z hzb]

/-- **The line law of the family is the closed strip of its fixed part.** For a finite divisor `Z`
without real points, symmetric under `ρ ↦ ρ̄` and `ρ ↦ 1 − ρ̄`: every member `Y ≥ 1` of the family
over `G_Z` satisfies the line law exactly when `Z` lies in the closed strip `0 ≤ Re ρ ≤ 1`. -/
theorem divisorPencil_lineLaw_iff {Z : Multiset ℂ} (hconj : Z.map (starRingEnd ℂ) = Z)
    (hsymm : Z.map (fun ρ => 1 - (starRingEnd ℂ) ρ) = Z) (hnr : ∀ ρ ∈ Z, ρ.im ≠ 0) :
    (∀ ρ ∈ Z, 0 ≤ ρ.re) ↔
      ∀ Y : ℝ, 1 ≤ Y → ∀ s : ℂ, s.re ≠ 1 / 2 → pencil (divisorPoly Z) Y s = 0 → s.im = 0 := by
  constructor
  · intro hstrip Y hY s hre h
    exact divisorPencil_lineLaw hconj hsymm hstrip (fun h1 => hnr 1 h1 (by simp)) hY hre h
  · intro hlaw ρ hρ
    by_contra hneg
    have hρneg : ρ.re < 0 := not_le.mp hneg
    have hρ' : 1 - (starRingEnd ℂ) ρ ∈ Z := by
      rw [← hsymm]
      exact Multiset.mem_map_of_mem _ hρ
    obtain ⟨a, ha⟩ := Infinite.exists_notMem_finset Z.toFinset
    have ha' : divisorPoly Z a ≠ 0 := fun h0 =>
      ha (Multiset.mem_toFinset.mpr (divisorPoly_eq_zero_iff.mp h0))
    obtain ⟨Y₀, hY₀⟩ := exists_nonreal_zero_pencil_of_zero_right (differentiable_divisorPoly Z)
      ha' (divisorPoly_eq_zero_iff.mpr hρ')
      (by simp only [sub_re, one_re, conj_re]; linarith)
      (by simpa using hnr ρ hρ)
    obtain ⟨s, hs, him, hz⟩ := hY₀ (max Y₀ 1) (le_max_left _ _)
    have hs' : (1 : ℝ) / 2 < s.re := hs
    exact him (hlaw (max Y₀ 1) (le_max_right _ _) s (ne_of_gt hs') hz)

end

end GaloisForLFunctions.InfiniteRankPurityTheory
