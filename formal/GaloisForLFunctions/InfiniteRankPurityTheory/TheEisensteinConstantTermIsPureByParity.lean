import GaloisForLFunctions.InfiniteRankPurityTheory.ADefectOfIndexOneIsPureOffTheRealAxis
import GaloisForLFunctions.BlackHoleRingdown.TheReflectedSignalIsTheEchoTrain

/-!
# The Eisenstein constant term is pure by parity

For `Y ≥ 1` the constant term of the completed Eisenstein series at height `Y`,

`a_Y(s) = Λ(2s) Y^s + Λ(2s − 1) Y^{1−s}`,   `Λ = Γ_ℝ ζ`,

has no non-real zero off the line `Re s = ½`, and at most one zero right of the line
(`lineLaw`, `constantTerm_zero_subsingleton`). No truncated Eisenstein series enters.

**Proof.** Clear the poles: `s(s−1)(2s−1) a_Y(s) = (s−1) E(s) + s E'(s)` with
`E(s) = ξ(2s) Y^s`, `E'(s) = ξ(2s−1) Y^{1−s}`.
- `E` does not vanish on `Re s > ½`, since `ζ` has no zero on `Re ≥ 1`.
- `‖E'‖ ≤ ‖E‖` there: every zero of `ξ` lies left of `Re = 1`, so reflection in that line
  decreases `‖ξ‖` (Hadamard product), and `Y^{1−σ} ≤ Y^σ`.
- Hence `θ = E'/E` is a real Schur function on the half-plane, and a zero of `a_Y` right of the line
  is a point where `θ = −(s−1)/s`. The factor `(s−1)/s` is the defect of the pole of `ζ`: one point on
  the wrong side.
- A defect of index one admits at most one such point, and it is real
  (`hermiteBiehler_indexOne`). The functional equation carries this to the left of the line.

The structures used: the functional equation (reflection), the Euler product only through
`ζ ≠ 0` on `Re ≥ 1`, the pole as one negative square, and reality.
-/

open Complex Set

namespace GaloisForLFunctions.InfiniteRankPurityTheory

open _root_.RHTower GaloisForLFunctions.BlackHoleRingdown

noncomputable section

/-- The right half `E(s) = ξ(2s) Y^s` of the constant term. -/
def constantTermHalf (Y : ℝ) (s : ℂ) : ℂ := xi (2 * s) * (Y : ℂ) ^ s

/-- The reflected half `E'(s) = ξ(2s − 1) Y^{1−s} = E(1 − s)`. -/
def constantTermDual (Y : ℝ) (s : ℂ) : ℂ := xi (2 * s - 1) * (Y : ℂ) ^ (1 - s)

/-- The constant term with its poles cleared: `(s − 1) ξ(2s) Y^s + s ξ(2s − 1) Y^{1−s}`. -/
def constantTerm (Y : ℝ) (s : ℂ) : ℂ :=
  (s - 1) * constantTermHalf Y s + s * constantTermDual Y s

theorem constantTermDual_eq (Y : ℝ) (s : ℂ) :
    constantTermDual Y s = constantTermHalf Y (1 - s) := by
  rw [constantTermDual, constantTermHalf,
    show 2 * (1 - s) = 1 - (2 * s - 1) by ring, xi_one_sub]

/-- The cleared constant term is odd under `s ↦ 1 − s`. -/
theorem constantTerm_one_sub (Y : ℝ) (s : ℂ) : constantTerm Y (1 - s) = -constantTerm Y s := by
  rw [constantTerm, constantTerm, constantTermDual_eq, constantTermDual_eq, sub_sub_cancel]
  ring

theorem cpow_conj_of_pos {Y : ℝ} (hY : 0 < Y) (s : ℂ) :
    (Y : ℂ) ^ (starRingEnd ℂ) s = (starRingEnd ℂ) ((Y : ℂ) ^ s) := by
  have harg : (Y : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hY.le]
    exact Real.pi_pos.ne
  rw [Complex.cpow_conj _ _ harg, Complex.conj_ofReal]

theorem constantTermHalf_conj {Y : ℝ} (hY : 0 < Y) (s : ℂ) :
    constantTermHalf Y ((starRingEnd ℂ) s) = (starRingEnd ℂ) (constantTermHalf Y s) := by
  have h2 : (2 : ℂ) * (starRingEnd ℂ) s = (starRingEnd ℂ) (2 * s) := by
    rw [map_mul, Complex.conj_ofNat]
  rw [constantTermHalf, constantTermHalf, map_mul, h2, xi_conj, cpow_conj_of_pos hY]

theorem constantTermDual_conj {Y : ℝ} (hY : 0 < Y) (s : ℂ) :
    constantTermDual Y ((starRingEnd ℂ) s) = (starRingEnd ℂ) (constantTermDual Y s) := by
  rw [constantTermDual_eq, constantTermDual_eq, ← constantTermHalf_conj hY]
  simp

theorem differentiable_constantTermHalf {Y : ℝ} (hY : 0 < Y) :
    Differentiable ℂ (constantTermHalf Y) := by
  have hY0 : (Y : ℂ) ≠ 0 := by exact_mod_cast hY.ne'
  intro s
  have h1 : DifferentiableAt ℂ (fun s : ℂ => xi (2 * s)) s :=
    (xi_differentiable (2 * s)).comp s (by fun_prop)
  have h2 : DifferentiableAt ℂ (fun s : ℂ => (Y : ℂ) ^ s) s :=
    differentiableAt_id.const_cpow (Or.inl hY0)
  exact h1.mul h2

theorem differentiable_constantTermDual {Y : ℝ} (hY : 0 < Y) :
    Differentiable ℂ (constantTermDual Y) := by
  have h : constantTermDual Y = fun s => constantTermHalf Y (1 - s) := by
    funext s
    exact constantTermDual_eq Y s
  rw [h]
  exact (differentiable_constantTermHalf hY).comp (by fun_prop)

/-- `E` has no zero right of the line: `ζ` has none on `Re ≥ 1`. -/
theorem constantTermHalf_ne_zero {Y : ℝ} (hY : 0 < Y) {s : ℂ} (hs : s ∈ rightHalf) :
    constantTermHalf Y s ≠ 0 := by
  have hY0 : (Y : ℂ) ≠ 0 := by exact_mod_cast hY.ne'
  have h1 : (1 : ℝ) / 2 < s.re := hs
  refine mul_ne_zero (xi_ne_zero_of_one_le_re ?_) (Complex.cpow_ne_zero_iff.mpr (Or.inl hY0))
  simp only [mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]
  linarith

/-- **The Schur bound.** For `Y ≥ 1` and `Re s > ½`: `‖ξ(2s−1) Y^{1−s}‖ ≤ ‖ξ(2s) Y^s‖`. -/
theorem norm_constantTermDual_le {Y : ℝ} (hY : 1 ≤ Y) {s : ℂ} (hs : s ∈ rightHalf) :
    ‖constantTermDual Y s‖ ≤ ‖constantTermHalf Y s‖ := by
  have hY0 : 0 < Y := by linarith
  have h1 : (1 : ℝ) / 2 < s.re := hs
  have hw : 0 ≤ (s - 1 / 2).re := by
    simp only [sub_re, one_div, inv_re, re_ofNat, normSq_ofNat, div_self_mul_self']
    linarith
  have hxi := norm_xi_two_mul_le hw
  rw [show 2 * (s - 1 / 2) = 2 * s - 1 by ring, show 1 + (2 * s - 1) = 2 * s by ring] at hxi
  rw [constantTermDual, constantTermHalf, norm_mul, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hY0, Complex.norm_cpow_eq_rpow_re_of_pos hY0]
  have hpow : Y ^ (1 - s).re ≤ Y ^ s.re := by
    apply Real.rpow_le_rpow_of_exponent_le hY
    simp only [sub_re, one_re]
    linarith
  exact mul_le_mul hxi hpow (Real.rpow_nonneg hY0.le _) (norm_nonneg _)

theorem constantTerm_one {Y : ℝ} (hY : 0 < Y) : constantTerm Y 1 = 1 / 2 := by
  have hY0 : (Y : ℂ) ≠ 0 := by exact_mod_cast hY.ne'
  rw [constantTerm, constantTermDual]
  norm_num [xi_one]

theorem one_mem_rightHalf : (1 : ℂ) ∈ rightHalf := by
  show (1 : ℝ) / 2 < (1 : ℂ).re
  norm_num

/-- The index-one data of the constant term: at most one zero right of the line, and it is
real. -/
theorem constantTerm_indexOne {Y : ℝ} (hY : 1 ≤ Y) :
    {s | s ∈ rightHalf ∧ constantTerm Y s = 0}.Subsingleton ∧
      ∀ s ∈ rightHalf, constantTerm Y s = 0 → s.im = 0 := by
  have hY0 : 0 < Y := by linarith
  have hform : ∀ s : ℂ, constantTerm Y s =
      (s - 1) * constantTermHalf Y s - (-1 : ℂ) * (s - (1 - 1)) * constantTermDual Y s := by
    intro s
    rw [constantTerm]
    ring
  have hdiff : ∃ z ∈ rightHalf,
      (z - 1) * constantTermHalf Y z - (-1 : ℂ) * (z - (1 - 1)) * constantTermDual Y z ≠ 0 := by
    refine ⟨1, one_mem_rightHalf, ?_⟩
    rw [← hform, constantTerm_one hY0]
    norm_num
  have h := hermiteBiehler_indexOne (E := constantTermHalf Y) (E' := constantTermDual Y)
    (w := 1) (c := -1)
    (differentiable_constantTermHalf hY0).differentiableOn
    (differentiable_constantTermDual hY0).differentiableOn
    (fun s hs => constantTermHalf_ne_zero hY0 hs)
    (fun s hs => norm_constantTermDual_le hY hs)
    (fun s _ => constantTermHalf_conj hY0 s) (fun s _ => constantTermDual_conj hY0 s)
    one_mem_rightHalf (map_one _) (by simp) (by simp) hdiff
  simp only [← hform] at h
  exact h

/-- **At most one exceptional parameter.** For `Y ≥ 1` the cleared constant term has at most one
zero right of the line. -/
theorem constantTerm_zero_subsingleton {Y : ℝ} (hY : 1 ≤ Y) :
    {s | s ∈ rightHalf ∧ constantTerm Y s = 0}.Subsingleton :=
  (constantTerm_indexOne hY).1

/-- **The line law.** For `Y ≥ 1` every zero of the cleared constant term off the line
`Re s = ½` is real. -/
theorem im_eq_zero_of_constantTerm_eq_zero {Y : ℝ} (hY : 1 ≤ Y) {s : ℂ}
    (hre : s.re ≠ 1 / 2) (h : constantTerm Y s = 0) : s.im = 0 := by
  rcases lt_or_gt_of_ne hre with hlt | hgt
  · have hmem : 1 - s ∈ rightHalf := by
      show (1 : ℝ) / 2 < (1 - s).re
      simp only [sub_re, one_re]
      linarith
    have h0 : constantTerm Y (1 - s) = 0 := by rw [constantTerm_one_sub, h, neg_zero]
    have := (constantTerm_indexOne hY).2 (1 - s) hmem h0
    simpa using this
  · exact (constantTerm_indexOne hY).2 s hgt h

/-- The cleared constant term is `s(s−1)(2s−1)` times `Λ(2s) Y^s + Λ(2s−1) Y^{1−s}`. -/
theorem constantTerm_eq_completed (Y : ℝ) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) (h2 : s ≠ 1 / 2) :
    constantTerm Y s = s * (s - 1) * (2 * s - 1) *
      (completedRiemannZeta (2 * s) * (Y : ℂ) ^ s +
        completedRiemannZeta (2 * s - 1) * (Y : ℂ) ^ (1 - s)) := by
  have a0 : (2 : ℂ) * s ≠ 0 := mul_ne_zero two_ne_zero h0
  have a1 : (2 : ℂ) * s ≠ 1 := by
    intro h
    apply h2
    linear_combination h / 2
  have b0 : (2 : ℂ) * s - 1 ≠ 0 := fun h => a1 (by linear_combination h)
  have b1 : (2 : ℂ) * s - 1 ≠ 1 := by
    intro h
    apply h1
    linear_combination h / 2
  rw [constantTerm, constantTermHalf, constantTermDual, xi_eq_half_mul a0 a1,
    xi_eq_half_mul b0 b1]
  ring

/-- **The Lagarias–Suzuki line law, for every `Y ≥ 1` and every non-real `s` off the line.**
`Λ(2s) Y^s + Λ(2s − 1) Y^{1−s} ≠ 0`. -/
theorem lineLaw {Y : ℝ} (hY : 1 ≤ Y) {s : ℂ} (hre : s.re ≠ 1 / 2) (him : s.im ≠ 0) :
    completedRiemannZeta (2 * s) * (Y : ℂ) ^ s +
      completedRiemannZeta (2 * s - 1) * (Y : ℂ) ^ (1 - s) ≠ 0 := by
  intro h
  have h0 : s ≠ 0 := fun h => him (by rw [h]; simp)
  have h1 : s ≠ 1 := fun h => him (by rw [h]; simp)
  have h2 : s ≠ 1 / 2 := fun h => hre (by rw [h]; norm_num)
  have hz : constantTerm Y s = 0 := by rw [constantTerm_eq_completed Y h0 h1 h2, h, mul_zero]
  exact him (im_eq_zero_of_constantTerm_eq_zero hY hre hz)

/-- The same law in the form `Λ = Γ_ℝ ζ`. -/
theorem lineLaw_gammaZeta {Y : ℝ} (hY : 1 ≤ Y) {s : ℂ} (hre : s.re ≠ 1 / 2) (him : s.im ≠ 0) :
    Complex.Gammaℝ (2 * s) * riemannZeta (2 * s) * (Y : ℂ) ^ s +
      Complex.Gammaℝ (2 * s - 1) * riemannZeta (2 * s - 1) * (Y : ℂ) ^ (1 - s) ≠ 0 := by
  have him2 : (2 * s).im ≠ 0 := by simpa using him
  have him3 : (2 * s - 1).im ≠ 0 := by simpa using him
  have key : ∀ w : ℂ, w.im ≠ 0 → Complex.Gammaℝ w * riemannZeta w = completedRiemannZeta w := by
    intro w hw
    have hw0 : w ≠ 0 := fun h => hw (by rw [h]; simp)
    have hΓ : Complex.Gammaℝ w ≠ 0 := by
      intro h
      obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp h
      apply hw
      rw [hn]
      simp
    rw [riemannZeta_def_of_ne_zero hw0, mul_div_cancel₀ _ hΓ]
  rw [key _ him2, key _ him3]
  exact lineLaw hY hre him

end

end GaloisForLFunctions.InfiniteRankPurityTheory

#print axioms GaloisForLFunctions.InfiniteRankPurityTheory.lineLaw
#print axioms GaloisForLFunctions.InfiniteRankPurityTheory.constantTerm_zero_subsingleton
