import GaloisForLFunctions.RHTower.WeilPositivityTwistObstruction

/-!
# The theta kernel of an even Dirichlet character on the critical axis

For an even Dirichlet character `χ` mod `q > 1`, `χ ≠ 1`, let
`K_χ(x) = ∑_j χ(j) evenKernel(j/q)(x)` (mathlib's even Hurwitz theta kernels) and
`Φ_χ(u) = e^{u/2} K_χ(e^{2u})`.

* **Decay** (`exists_norm_dirichletAxisKernel_le`).  For every `B ≥ 0`,
  `‖Φ_χ(u)‖ ≤ C_B e^{-B|u|}`.  At `+∞` each Hurwitz kernel decays exponentially and the
  pole correction at `j = 0` is killed by `χ(0) = 0`.  At `-∞` the kernel functional equation
  turns `K_χ` into `x^{-1/2} ∑_j χ(j)(cosKernel(j/q)(1/x) - 1)`, using `∑_j χ(j) = 0`.
* **Transform** (`paperFT_dirichletAxisKernel`).  `∫ Φ_χ(u) e^{izu} du = q^s Λ(s, χ)` with
  `s = 1/2 + iz`, for every complex `z`.  On `Re s > 1` this is the Mellin representation of the
  completed Hurwitz zeta functions; both sides are entire.
* Hence `Φ_χ` lies in the radical of `L(s, χ)`
  (`paperFT_dirichletAxisKernel_gammaOf_eq_zero`), and its transform is nonzero at `s = 5/4`.
-/

open Complex MeasureTheory Real Set Filter Topology Asymptotics
open scoped ComplexConjugate

noncomputable section
namespace RHTower

open Zeta23 HurwitzZeta

variable {q : ℕ} [NeZero q]

/-! ### The theta kernel of an even Dirichlet character -/

/-- `K_χ(x) = ∑_j χ(j) evenKernel(j/q)(x)`: the theta function of an even Dirichlet character. -/
def dirichletThetaKernel (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  ∑ j : ZMod q, χ j * (evenKernel (ZMod.toAddCircle j) x : ℂ)

/-- The axis kernel `Φ_χ(u) = e^{u/2} K_χ(e^{2u})`. -/
def dirichletAxisKernel (χ : DirichletCharacter ℂ q) (u : ℝ) : ℂ :=
  (Real.exp (u / 2) : ℂ) * dirichletThetaKernel χ (Real.exp (2 * u))

theorem continuous_dirichletAxisKernel (χ : DirichletCharacter ℂ q) :
    Continuous (dirichletAxisKernel χ) := by
  unfold dirichletAxisKernel dirichletThetaKernel
  refine (by fun_prop : Continuous fun u : ℝ => (Real.exp (u / 2) : ℂ)).mul ?_
  refine continuous_finsetSum _ fun j _ => continuous_const.mul ?_
  refine Complex.continuous_ofReal.comp ?_
  exact (continuousOn_evenKernel _).comp_continuous (by fun_prop) fun u => Real.exp_pos _

omit [NeZero q] in
theorem dirichlet_character_zero_eq_zero (hq : 1 < q) (χ : DirichletCharacter ℂ q) : χ 0 = 0 := by
  haveI : Fact (1 < q) := ⟨hq⟩
  exact MulChar.map_nonunit χ not_isUnit_zero

/-- The pole-correction term of each even Hurwitz kernel is killed by `χ`. -/
theorem dirichlet_mul_f₀_eq_zero (hq : 1 < q) (χ : DirichletCharacter ℂ q) (j : ZMod q) :
    χ j * (if ZMod.toAddCircle j = 0 then (1 : ℂ) else 0) = 0 := by
  split_ifs with h
  · rw [ZMod.toAddCircle_eq_zero.mp h, dirichlet_character_zero_eq_zero hq, zero_mul]
  · rw [mul_zero]

/-- `exp(u/2) exp(-p e^{2u}) ≤ C e^{-Bu}` for `u ≥ 0`. -/
theorem exists_exp_half_mul_exp_neg_exp_le {p : ℝ} (hp : 0 < p) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, 0 ≤ u →
      Real.exp (u / 2) * Real.exp (-(p * Real.exp (2 * u))) ≤ C * Real.exp (-(B * u)) := by
  set N : ℕ := ⌈|B|⌉₊ + 1 with hN
  refine ⟨(N.factorial : ℝ) / p ^ N, by positivity, fun u hu => ?_⟩
  set y := p * Real.exp (2 * u) with hy
  have hy0 : 0 ≤ y := by positivity
  have hfac := Real.pow_div_factorial_le_exp y hy0 N
  have hNB : B + 1 / 2 ≤ 2 * N := by
    have h1 : |B| ≤ ⌈|B|⌉₊ := Nat.le_ceil _
    have h2 := le_abs_self B
    rw [hN]; push_cast; linarith
  have hexp : Real.exp ((B + 1 / 2) * u) ≤ (y / p) ^ N := by
    rw [hy, mul_div_cancel_left₀ _ hp.ne', ← Real.exp_nat_mul]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have key : Real.exp (u / 2) * Real.exp (-y) * Real.exp (B * u) ≤ (N.factorial : ℝ) / p ^ N := by
    have e1 : Real.exp (u / 2) * Real.exp (-y) * Real.exp (B * u) =
        Real.exp ((B + 1 / 2) * u) * Real.exp (-y) := by
      rw [mul_right_comm, ← Real.exp_add]; congr 1; ring_nf
    rw [e1]
    have hpN : 0 < p ^ N := by positivity
    calc Real.exp ((B + 1 / 2) * u) * Real.exp (-y) ≤ (y / p) ^ N * Real.exp (-y) :=
          mul_le_mul_of_nonneg_right hexp (Real.exp_pos _).le
      _ = y ^ N / p ^ N * Real.exp (-y) := by rw [div_pow]
      _ ≤ (N.factorial : ℝ) / p ^ N := by
          rw [Real.exp_neg, div_mul_eq_mul_div, mul_comm]
          rw [div_le_div_iff_of_pos_right hpN]
          have h1 := (div_le_iff₀ (by positivity : (0 : ℝ) < N.factorial)).mp hfac
          have h2 : (Real.exp y)⁻¹ * y ^ N ≤ (Real.exp y)⁻¹ * (Real.exp y * N.factorial) :=
            mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr (Real.exp_pos _).le)
          rw [← mul_assoc, inv_mul_cancel₀ (Real.exp_pos y).ne', one_mul] at h2
          exact h2
  have hpos : 0 < Real.exp (B * u) := Real.exp_pos _
  have e2 : Real.exp (-(B * u)) = 1 / Real.exp (B * u) := by rw [Real.exp_neg, one_div]
  rw [e2, ← div_eq_mul_one_div, le_div_iff₀ hpos]
  exact key

/-- Exponential decay of `K_χ` at `+∞`. -/
theorem exists_dirichletThetaKernel_atTop (hq : 1 < q) (χ : DirichletCharacter ℂ q) :
    ∃ p : ℝ, 0 < p ∧ (dirichletThetaKernel χ) =O[atTop] (fun x => Real.exp (-p * x)) := by
  have hj := fun j : ZMod q => isBigO_atTop_evenKernel_sub (ZMod.toAddCircle j)
  choose P hP hPO using hj
  set p := Finset.univ.inf' Finset.univ_nonempty P with hpdef
  have hp : 0 < p := (Finset.lt_inf'_iff _).mpr fun j _ => hP j
  refine ⟨p, hp, ?_⟩
  have hterm : ∀ j ∈ (Finset.univ : Finset (ZMod q)),
      (fun x : ℝ => χ j * (((evenKernel (ZMod.toAddCircle j) x -
        (if ZMod.toAddCircle j = 0 then 1 else 0) : ℝ)) : ℂ)) =O[atTop]
        (fun x => Real.exp (-p * x)) := by
    intro j _
    have h1 := (isBigO_ofReal_left.mpr (hPO j)).const_mul_left (χ j)
    refine h1.trans (IsBigO.of_bound 1 ?_)
    filter_upwards [eventually_ge_atTop 0] with x hx
    rw [one_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_exp.mpr (by nlinarith [Finset.inf'_le P (Finset.mem_univ j)])
  refine (IsBigO.sum hterm).congr_left fun x => ?_
  unfold dirichletThetaKernel
  refine Finset.sum_congr rfl fun j _ => ?_
  have := dirichlet_mul_f₀_eq_zero hq χ j
  push_cast
  rw [mul_sub, ← (show χ j * (if ZMod.toAddCircle j = 0 then (1 : ℂ) else 0) =
    χ j * ((if ZMod.toAddCircle j = 0 then 1 else 0 : ℝ) : ℂ) by split_ifs <;> simp), this,
    sub_zero]

/-- Near `0`, `K_χ(x) = x^{-1/2} ∑_j χ(j)(cosKernel(j/q)(1/x) - 1)` for nontrivial `χ`. -/
theorem dirichletThetaKernel_eq_cos {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (x : ℝ) :
    dirichletThetaKernel χ x = ((1 / x ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
      ∑ j : ZMod q, χ j * ((cosKernel (ZMod.toAddCircle j) (1 / x) - 1 : ℝ) : ℂ) := by
  unfold dirichletThetaKernel
  have hsum : ∑ j : ZMod q, χ j = 0 := MulChar.sum_eq_zero_of_ne_one hχ
  simp only [evenKernel_functional_equation, Complex.ofReal_mul, Complex.ofReal_sub,
    Complex.ofReal_one, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [show ∑ j : ZMod q, ((1 / x ^ (1 / 2 : ℝ) : ℝ) : ℂ) * (χ j * 1) =
    ((1 / x ^ (1 / 2 : ℝ) : ℝ) : ℂ) * ∑ j : ZMod q, χ j by rw [Finset.mul_sum]; simp, hsum,
    mul_zero, sub_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem exists_dirichletCos_atTop (χ : DirichletCharacter ℂ q) :
    ∃ p : ℝ, 0 < p ∧ (fun y : ℝ => ∑ j : ZMod q, χ j *
      ((cosKernel (ZMod.toAddCircle j) y - 1 : ℝ) : ℂ)) =O[atTop] (fun y => Real.exp (-p * y)) := by
  have hj := fun j : ZMod q => isBigO_atTop_cosKernel_sub (ZMod.toAddCircle j)
  choose P hP hPO using hj
  set p := Finset.univ.inf' Finset.univ_nonempty P with hpdef
  have hp : 0 < p := (Finset.lt_inf'_iff _).mpr fun j _ => hP j
  refine ⟨p, hp, IsBigO.sum fun j _ => ?_⟩
  have h1 := (isBigO_ofReal_left.mpr (hPO j)).const_mul_left (χ j)
  refine h1.trans (IsBigO.of_bound 1 ?_)
  filter_upwards [eventually_ge_atTop 0] with x hx
  rw [one_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_le_exp.mpr (by nlinarith [Finset.inf'_le P (Finset.mem_univ j)])

/-- **Super-exponential decay of the axis kernel.**  For every `B ≥ 0` there is `C` with
`‖Φ_χ(u)‖ ≤ C e^{-B|u|}`. -/
theorem exists_norm_dirichletAxisKernel_le (hq : 1 < q) {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, ‖dirichletAxisKernel χ u‖ ≤ C * Real.exp (-(B * |u|)) := by
  obtain ⟨p, hp, hO⟩ := exists_dirichletThetaKernel_atTop hq χ
  obtain ⟨p', hp', hO'⟩ := exists_dirichletCos_atTop χ
  obtain ⟨c, hc⟩ := hO.bound
  obtain ⟨c', hc'⟩ := hO'.bound
  obtain ⟨x₀, hx₀⟩ := (eventually_atTop.mp hc)
  obtain ⟨y₀, hy₀⟩ := (eventually_atTop.mp hc')
  obtain ⟨CB, hCB0, hCB⟩ := exists_exp_half_mul_exp_neg_exp_le hp B
  obtain ⟨CB', hCB'0, hCB'⟩ := exists_exp_half_mul_exp_neg_exp_le hp' B
  set u₁ := max 0 (Real.log (max x₀ 1) / 2) with hu₁
  set u₂ := min 0 (-(Real.log (max y₀ 1) / 2)) with hu₂
  -- the compact middle
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := u₂) (b := u₁)).exists_bound_of_continuousOn
    (continuous_dirichletAxisKernel χ).continuousOn
  set U := max |u₁| |u₂| with hU
  refine ⟨max (max (max c 0 * CB) (max c' 0 * CB')) (max M 0 * Real.exp (B * U)),
    by positivity, fun u => ?_⟩
  by_cases h1 : u₁ ≤ u
  · -- the right tail
    have hu0 : 0 ≤ u := le_trans (le_max_left _ _) h1
    have hx : x₀ ≤ Real.exp (2 * u) := by
      have : Real.log (max x₀ 1) ≤ 2 * u := by
        have := le_trans (le_max_right _ _) h1; linarith
      calc x₀ ≤ max x₀ 1 := le_max_left _ _
        _ = Real.exp (Real.log (max x₀ 1)) := (Real.exp_log (by positivity)).symm
        _ ≤ Real.exp (2 * u) := Real.exp_le_exp.mpr this
    have hK := hx₀ _ hx
    rw [Real.norm_of_nonneg (Real.exp_pos _).le] at hK
    unfold dirichletAxisKernel
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, abs_of_nonneg hu0]
    calc Real.exp (u / 2) * ‖dirichletThetaKernel χ (Real.exp (2 * u))‖
        ≤ Real.exp (u / 2) * (max c 0 * Real.exp (-p * Real.exp (2 * u))) := by
          gcongr; exact hK.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
      _ = max c 0 * (Real.exp (u / 2) * Real.exp (-(p * Real.exp (2 * u)))) := by ring_nf
      _ ≤ max c 0 * (CB * Real.exp (-(B * u))) :=
          mul_le_mul_of_nonneg_left (hCB u hu0) (le_max_right _ _)
      _ ≤ _ := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right (le_trans (le_max_left _ _) (le_max_left _ _))
            (Real.exp_pos _).le
  by_cases h2 : u ≤ u₂
  · -- the left tail, via the functional equation
    have hu0 : u ≤ 0 := le_trans h2 (min_le_left _ _)
    set v := -u with hv
    have hv0 : 0 ≤ v := by linarith
    have hy : y₀ ≤ 1 / Real.exp (2 * u) := by
      have : Real.log (max y₀ 1) ≤ 2 * v := by
        have := le_trans h2 (min_le_right _ _); linarith
      calc y₀ ≤ max y₀ 1 := le_max_left _ _
        _ = Real.exp (Real.log (max y₀ 1)) := (Real.exp_log (by positivity)).symm
        _ ≤ Real.exp (2 * v) := Real.exp_le_exp.mpr this
        _ = 1 / Real.exp (2 * u) := by rw [hv, one_div, ← Real.exp_neg]; ring_nf
    have hK := hy₀ _ hy
    rw [Real.norm_of_nonneg (Real.exp_pos _).le] at hK
    unfold dirichletAxisKernel
    rw [dirichletThetaKernel_eq_cos hχ, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le, abs_of_nonpos hu0]
    have hrpow : Real.exp (2 * u) ^ (1 / 2 : ℝ) = Real.exp u := by
      rw [← Real.exp_mul]; ring_nf
    rw [hrpow, Real.norm_of_nonneg (by positivity)]
    have hexp : Real.exp (u / 2) * (1 / Real.exp u) = Real.exp (v / 2) := by
      rw [one_div, ← Real.exp_neg, ← Real.exp_add, hv]; ring_nf
    have hey : 1 / Real.exp (2 * u) = Real.exp (2 * v) := by
      rw [hv, one_div, ← Real.exp_neg]; ring_nf
    calc Real.exp (u / 2) * (1 / Real.exp u *
          ‖∑ j : ZMod q, χ j * ((cosKernel (ZMod.toAddCircle j) (1 / Real.exp (2 * u)) - 1 : ℝ) : ℂ)‖)
        ≤ Real.exp (u / 2) * (1 / Real.exp u *
            (max c' 0 * Real.exp (-p' * (1 / Real.exp (2 * u))))) := by
          gcongr
          exact hK.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
      _ = max c' 0 * (Real.exp (v / 2) * Real.exp (-(p' * Real.exp (2 * v)))) := by
          rw [← hexp, hey]; ring_nf
      _ ≤ max c' 0 * (CB' * Real.exp (-(B * v))) :=
          mul_le_mul_of_nonneg_left (hCB' v hv0) (le_max_right _ _)
      _ ≤ _ := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right (le_trans (le_max_right _ _) (le_max_left _ _))
            (Real.exp_pos _).le
  · -- the compact middle
    push Not at h1 h2
    have hmem : u ∈ Icc u₂ u₁ := ⟨h2.le, h1.le⟩
    have hb := hM u hmem
    have habs : |u| ≤ U := by
      rw [abs_le]; constructor
      · have := le_max_right |u₁| |u₂|; have := neg_abs_le u₂; linarith [h2]
      · have := le_max_left |u₁| |u₂|; have := le_abs_self u₁; linarith [h1]
    have hexp : 1 ≤ Real.exp (B * U) * Real.exp (-(B * |u|)) := by
      rw [← Real.exp_add]; exact Real.one_le_exp (by nlinarith)
    calc ‖dirichletAxisKernel χ u‖ ≤ max M 0 := hb.trans (le_max_left _ _)
      _ ≤ max M 0 * (Real.exp (B * U) * Real.exp (-(B * |u|))) := le_mul_of_one_le_right
          (le_max_right _ _) hexp
      _ = max M 0 * Real.exp (B * U) * Real.exp (-(B * |u|)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le

/-! ### The transform of the axis kernel -/

theorem superExpDecay_dirichletAxisKernel (hq : 1 < q) {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) : SuperExpDecay (dirichletAxisKernel χ) := by
  refine ⟨continuous_dirichletAxisKernel χ, fun c => ?_⟩
  obtain ⟨C, hC0, hC⟩ := exists_norm_dirichletAxisKernel_le hq hχ (B := |c| + 1) (by positivity)
  refine Integrable.mono' ((integrable_exp_neg_mul_abs_modSource (a := 1) one_pos).const_mul C)
    ((continuous_dirichletAxisKernel χ).norm.mul (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ‖dirichletAxisKernel χ u‖ * Real.exp (c * |u|)
      ≤ C * Real.exp (-((|c| + 1) * |u|)) * Real.exp (c * |u|) :=
        mul_le_mul_of_nonneg_right (hC u) (Real.exp_pos _).le
    _ = C * Real.exp (-((|c| + 1) * |u|) + c * |u|) := by rw [mul_assoc, ← Real.exp_add]
    _ ≤ C * Real.exp (-1 * |u|) := by
        gcongr
        nlinarith [le_abs_self c, abs_nonneg u]

theorem hurwitzEvenFEPair_hasMellin {a : UnitAddCircle} (ha : a ≠ 0) {w : ℂ} (hw : 1 / 2 < w.re) :
    HasMellin (fun x : ℝ => (evenKernel a x : ℂ)) w ((hurwitzEvenFEPair a).Λ w) := by
  have h := (hurwitzEvenFEPair a).hasMellin (s := w) (by simpa [hurwitzEvenFEPair] using hw)
  have hf : (fun x => (hurwitzEvenFEPair a).f x - (hurwitzEvenFEPair a).f₀) =
      fun x : ℝ => (evenKernel a x : ℂ) := by
    funext x; simp [hurwitzEvenFEPair, ha]
  rwa [hf] at h

/-- On `Re s > 1` the transform of the axis kernel is `q^s Λ(s, χ)`. -/
theorem paperFT_dirichletAxisKernel_of_re (hq : 1 < q) {χ : DirichletCharacter ℂ q}
    (heven : χ.Even) {z : ℂ} (hz : 1 < (1 / 2 + I * z).re) :
    paperFT (dirichletAxisKernel χ) z = (q : ℂ) ^ (1 / 2 + I * z) *
      DirichletCharacter.completedLFunction χ (1 / 2 + I * z) := by
  set s := 1 / 2 + I * z with hs
  have hw : 1 / 2 < (s / 2).re := by
    have : (s / 2).re = s.re / 2 := by simp
    rw [this]; linarith
  -- step 1: the substitution `x = e^{2u}`
  have h1 : paperFT (dirichletAxisKernel χ) z =
      (1 / 2) * mellin (dirichletThetaKernel χ) (s / 2) := by
    rw [← integral_cexp_mul_comp_exp_two]
    unfold paperFT dirichletAxisKernel
    congr 1; funext u
    rw [mul_comm ((Real.exp (u / 2) : ℂ)) _, mul_assoc, mul_comm]
    congr 1
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1; rw [hs]; push_cast; ring
  -- step 2: linearity of the Mellin transform
  have hconv : ∀ j : ZMod q, χ j ≠ 0 → HasMellin (fun x : ℝ =>
      (evenKernel (ZMod.toAddCircle j) x : ℂ)) (s / 2)
        ((hurwitzEvenFEPair (ZMod.toAddCircle j)).Λ (s / 2)) := by
    intro j hj
    have hj0 : j ≠ 0 := fun h => hj (by rw [h, dirichlet_character_zero_eq_zero hq])
    exact hurwitzEvenFEPair_hasMellin (ZMod.toAddCircle_eq_zero.not.mpr hj0) hw
  have h2 : mellin (dirichletThetaKernel χ) (s / 2) =
      ∑ j : ZMod q, χ j * (2 * completedHurwitzZetaEven (ZMod.toAddCircle j) s) := by
    unfold mellin dirichletThetaKernel
    have hint : ∀ j ∈ (Finset.univ : Finset (ZMod q)), IntegrableOn (fun t : ℝ =>
        (t : ℂ) ^ (s / 2 - 1) • (χ j * (evenKernel (ZMod.toAddCircle j) t : ℂ))) (Ioi 0) := by
      intro j _
      by_cases hj : χ j = 0
      · simp [hj]
      · have h' : IntegrableOn (fun t : ℝ => χ j * ((t : ℂ) ^ (s / 2 - 1) •
            (evenKernel (ZMod.toAddCircle j) t : ℂ))) (Ioi 0) := ((hconv j hj).1).const_mul (χ j)
        refine h'.congr_fun (fun t _ => ?_) measurableSet_Ioi
        simp only [smul_eq_mul]; ring
    simp only [Finset.smul_sum]
    rw [integral_finsetSum _ hint]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : χ j = 0
    · simp [hj]
    · have hm := (hconv j hj).2
      unfold mellin at hm
      rw [show (fun t : ℝ => (t : ℂ) ^ (s / 2 - 1) • (χ j * (evenKernel (ZMod.toAddCircle j) t : ℂ)))
        = fun t : ℝ => χ j * ((t : ℂ) ^ (s / 2 - 1) • (evenKernel (ZMod.toAddCircle j) t : ℂ)) by
          funext t; simp only [smul_eq_mul]; ring,
        integral_const_mul, hm]
      unfold completedHurwitzZetaEven
      ring
  -- step 3: the completed L-function
  have h3 : ∑ j : ZMod q, χ j * (2 * completedHurwitzZetaEven (ZMod.toAddCircle j) s) =
      2 * ((q : ℂ) ^ s * DirichletCharacter.completedLFunction χ s) := by
    have hdef := ZMod.completedLFunction_def_even heven.to_fun s
    have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
    unfold DirichletCharacter.completedLFunction
    rw [hdef]
    have hh : (q : ℂ) ^ s * (q : ℂ) ^ (-s) = 1 := by
      rw [← Complex.cpow_add _ _ hq0, add_neg_cancel, Complex.cpow_zero]
    calc ∑ j : ZMod q, χ j * (2 * completedHurwitzZetaEven (ZMod.toAddCircle j) s)
        = 2 * ∑ j : ZMod q, χ j * completedHurwitzZetaEven (ZMod.toAddCircle j) s := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      _ = 2 * (((q : ℂ) ^ s * (q : ℂ) ^ (-s)) *
            ∑ j : ZMod q, χ j * completedHurwitzZetaEven (ZMod.toAddCircle j) s) := by
          rw [hh, one_mul]
      _ = _ := by ring
  rw [h1, h2, h3]; ring

/-- **The axis kernel lies in the radical of `L(s, χ)`**: its transform is `q^s Λ(s, χ)`,
`s = 1/2 + iz`, for every `z`. -/
theorem paperFT_dirichletAxisKernel (hq : 1 < q) {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    (heven : χ.Even) (z : ℂ) :
    paperFT (dirichletAxisKernel χ) z = (q : ℂ) ^ (1 / 2 + I * z) *
      DirichletCharacter.completedLFunction χ (1 / 2 + I * z) := by
  set G : ℂ → ℂ := fun z => (q : ℂ) ^ (1 / 2 + I * z) *
    DirichletCharacter.completedLFunction χ (1 / 2 + I * z) with hG
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  have hGd : Differentiable ℂ G := by
    intro w
    have h1 : DifferentiableAt ℂ (fun w : ℂ => (q : ℂ) ^ (1 / 2 + I * w)) w :=
      DifferentiableAt.const_cpow (by fun_prop) (Or.inl hq0)
    have h2 : DifferentiableAt ℂ (fun w : ℂ =>
        DirichletCharacter.completedLFunction χ (1 / 2 + I * w)) w :=
      ((DirichletCharacter.differentiable_completedLFunction hχ) _).comp w (by fun_prop)
    exact h1.mul h2
  have hF : Differentiable ℂ (paperFT (dirichletAxisKernel χ)) :=
    (superExpDecay_dirichletAxisKernel hq hχ).differentiable_paperFT
  have hanF : AnalyticOnNhd ℂ (paperFT (dirichletAxisKernel χ)) univ :=
    fun w _ => hF.analyticAt w
  have hanG : AnalyticOnNhd ℂ G univ := fun w _ => hGd.analyticAt w
  set w₀ : ℂ := -I with hw₀
  have hopen : IsOpen {w : ℂ | 1 < (1 / 2 + I * w).re} :=
    isOpen_lt continuous_const (Complex.continuous_re.comp (by fun_prop))
  have hw₀mem : 1 < (1 / 2 + I * w₀).re := by
    rw [hw₀]; simp
  have hev : paperFT (dirichletAxisKernel χ) =ᶠ[𝓝 w₀] G :=
    Filter.eventually_of_mem (hopen.mem_nhds hw₀mem) fun w hw =>
      paperFT_dirichletAxisKernel_of_re hq heven hw
  exact hanF.eqOn_of_preconnected_of_eventuallyEq hanG isPreconnected_univ (mem_univ _) hev
    (mem_univ z)

/-- The transform vanishes at every nontrivial zero of `L(s, χ)`. -/
theorem paperFT_dirichletAxisKernel_gammaOf_eq_zero (hq : 1 < q) {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (heven : χ.Even) {ρ : ℂ} (hρ : Zeta23.ThmE.IsNontrivialZeroL χ ρ) :
    paperFT (dirichletAxisKernel χ) (gammaOf ρ) = 0 := by
  rw [paperFT_dirichletAxisKernel hq hχ heven, half_add_I_mul_gammaOf]
  have hL := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ ρ
    (Or.inr (by omega))
  rw [hρ.1, heven.gammaFactor_def] at hL
  have hΓ : ρ.Gammaℝ ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hρ.2.1
  have : DirichletCharacter.completedLFunction χ ρ = 0 := by
    rcases (div_eq_zero_iff.mp hL.symm) with h | h
    · exact h
    · exact absurd h hΓ
  rw [this, mul_zero]

/-- The transform does not vanish at `z = -3i/4` (`s = 5/4`). -/
theorem paperFT_dirichletAxisKernel_ne_zero (hq : 1 < q) {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (heven : χ.Even) : paperFT (dirichletAxisKernel χ) (-(3 / 4 * I)) ≠ 0 := by
  rw [paperFT_dirichletAxisKernel hq hχ heven]
  have hz : 1 / 2 + I * -(3 / 4 * I) = (5 / 4 : ℂ) := by ring_nf; rw [Complex.I_sq]; ring
  rw [hz]
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  refine mul_ne_zero (by rw [Ne, Complex.cpow_eq_zero_iff]; tauto) ?_
  intro h
  have hL := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ (5 / 4)
    (Or.inr (by omega))
  rw [h, zero_div] at hL
  exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by norm_num) hL

end RHTower
