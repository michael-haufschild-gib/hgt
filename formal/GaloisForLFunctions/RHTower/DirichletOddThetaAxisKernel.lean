import GaloisForLFunctions.RHTower.DirichletEvenThetaAxisKernel

/-!
# The theta kernel of an odd Dirichlet character on the critical axis

For an odd Dirichlet character `χ` mod `q`, let `K_χ(x) = ∑_j χ(j) oddKernel(j/q)(x)`
(mathlib's odd Hurwitz theta kernels) and `Φ_χ(u) = e^{3u/2} K_χ(e^{2u})`.

* **Decay** (`exists_norm_dirichletOddAxisKernel_le`).  For every `B ≥ 0`,
  `‖Φ_χ(u)‖ ≤ C_B e^{-B|u|}`.  At `+∞` each odd Hurwitz kernel decays exponentially; at `-∞`
  the kernel functional equation `oddKernel a x = x^{-3/2} sinKernel a (1/x)` turns `Φ_χ(-v)`
  into `e^{3v/2} ∑_j χ(j) sinKernel(j/q)(e^{2v})`.  No pole correction occurs in the odd case.
* **Transform** (`paperFT_dirichletOddAxisKernel`).  `∫ Φ_χ(u) e^{izu} du = q^s Λ(s, χ)` with
  `s = 1/2 + iz`, for every complex `z`.  On `Re s > 2` this is the Mellin representation of the
  completed odd Hurwitz zeta functions at `(s + 1)/2`; both sides are entire.
* Hence `Φ_χ` lies in the radical of `L(s, χ)`
  (`paperFT_dirichletOddAxisKernel_gammaOf_eq_zero`), and its transform is nonzero at `s = 5/4`.
-/

open Complex MeasureTheory Real Set Filter Topology Asymptotics
open scoped ComplexConjugate

noncomputable section
namespace RHTower

open Zeta23 HurwitzZeta

variable {q : ℕ} [NeZero q]

/-! ### The theta kernel of an odd Dirichlet character -/

/-- `K_χ(x) = ∑_j χ(j) oddKernel(j/q)(x)`: the theta function of an odd Dirichlet character. -/
def dirichletOddThetaKernel (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  ∑ j : ZMod q, χ j * (oddKernel (ZMod.toAddCircle j) x : ℂ)

/-- The axis kernel `Φ_χ(u) = e^{3u/2} K_χ(e^{2u})`. -/
def dirichletOddAxisKernel (χ : DirichletCharacter ℂ q) (u : ℝ) : ℂ :=
  (Real.exp (3 * u / 2) : ℂ) * dirichletOddThetaKernel χ (Real.exp (2 * u))

theorem continuous_dirichletOddAxisKernel (χ : DirichletCharacter ℂ q) :
    Continuous (dirichletOddAxisKernel χ) := by
  unfold dirichletOddAxisKernel dirichletOddThetaKernel
  refine (by fun_prop : Continuous fun u : ℝ => (Real.exp (3 * u / 2) : ℂ)).mul ?_
  refine continuous_finsetSum _ fun j _ => continuous_const.mul ?_
  refine Complex.continuous_ofReal.comp ?_
  exact (continuousOn_oddKernel _).comp_continuous (by fun_prop) fun u => Real.exp_pos _

/-- `exp(3u/2) exp(-p e^{2u}) ≤ C e^{-Bu}` for `u ≥ 0`. -/
theorem exists_exp_three_half_mul_exp_neg_exp_le {p : ℝ} (hp : 0 < p) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, 0 ≤ u →
      Real.exp (3 * u / 2) * Real.exp (-(p * Real.exp (2 * u))) ≤ C * Real.exp (-(B * u)) := by
  obtain ⟨C, hC0, hC⟩ := exists_exp_half_mul_exp_neg_exp_le hp (B + 1)
  refine ⟨C, hC0, fun u hu => ?_⟩
  have h := mul_le_mul_of_nonneg_left (hC u hu) (Real.exp_pos u).le
  calc Real.exp (3 * u / 2) * Real.exp (-(p * Real.exp (2 * u)))
      = Real.exp u * (Real.exp (u / 2) * Real.exp (-(p * Real.exp (2 * u)))) := by
        rw [← mul_assoc, ← Real.exp_add (u), show u + u / 2 = 3 * u / 2 by ring]
    _ ≤ Real.exp u * (C * Real.exp (-((B + 1) * u))) := h
    _ = C * Real.exp (-(B * u)) := by
        rw [mul_left_comm, ← Real.exp_add]; congr 2; ring

/-- Exponential decay of `K_χ` at `+∞`. -/
theorem exists_dirichletOddThetaKernel_atTop (χ : DirichletCharacter ℂ q) :
    ∃ p : ℝ, 0 < p ∧ (dirichletOddThetaKernel χ) =O[atTop] (fun x => Real.exp (-p * x)) := by
  have hj := fun j : ZMod q => isBigO_atTop_oddKernel (ZMod.toAddCircle j)
  choose P hP hPO using hj
  set p := Finset.univ.inf' Finset.univ_nonempty P with hpdef
  have hp : 0 < p := (Finset.lt_inf'_iff _).mpr fun j _ => hP j
  refine ⟨p, hp, IsBigO.sum fun j _ => ?_⟩
  have h1 := (isBigO_ofReal_left.mpr (hPO j)).const_mul_left (χ j)
  refine h1.trans (IsBigO.of_bound 1 ?_)
  filter_upwards [eventually_ge_atTop 0] with x hx
  rw [one_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_le_exp.mpr (by nlinarith [Finset.inf'_le P (Finset.mem_univ j)])

/-- Near `0`, `K_χ(x) = x^{-3/2} ∑_j χ(j) sinKernel(j/q)(1/x)`. -/
theorem dirichletOddThetaKernel_eq_sin (χ : DirichletCharacter ℂ q) (x : ℝ) :
    dirichletOddThetaKernel χ x = ((1 / x ^ (3 / 2 : ℝ) : ℝ) : ℂ) *
      ∑ j : ZMod q, χ j * (sinKernel (ZMod.toAddCircle j) (1 / x) : ℂ) := by
  unfold dirichletOddThetaKernel
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [oddKernel_functional_equation]
  push_cast; ring

theorem exists_dirichletSin_atTop (χ : DirichletCharacter ℂ q) :
    ∃ p : ℝ, 0 < p ∧ (fun y : ℝ => ∑ j : ZMod q, χ j *
      (sinKernel (ZMod.toAddCircle j) y : ℂ)) =O[atTop] (fun y => Real.exp (-p * y)) := by
  have hj := fun j : ZMod q => isBigO_atTop_sinKernel (ZMod.toAddCircle j)
  choose P hP hPO using hj
  set p := Finset.univ.inf' Finset.univ_nonempty P with hpdef
  have hp : 0 < p := (Finset.lt_inf'_iff _).mpr fun j _ => hP j
  refine ⟨p, hp, IsBigO.sum fun j _ => ?_⟩
  have h1 := (isBigO_ofReal_left.mpr (hPO j)).const_mul_left (χ j)
  refine h1.trans (IsBigO.of_bound 1 ?_)
  filter_upwards [eventually_ge_atTop 0] with x hx
  rw [one_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_le_exp.mpr (by nlinarith [Finset.inf'_le P (Finset.mem_univ j)])

/-- **Super-exponential decay of the odd axis kernel.**  For every `B ≥ 0` there is `C` with
`‖Φ_χ(u)‖ ≤ C e^{-B|u|}`. -/
theorem exists_norm_dirichletOddAxisKernel_le (χ : DirichletCharacter ℂ q) {B : ℝ} (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, ‖dirichletOddAxisKernel χ u‖ ≤ C * Real.exp (-(B * |u|)) := by
  obtain ⟨p, hp, hO⟩ := exists_dirichletOddThetaKernel_atTop χ
  obtain ⟨p', hp', hO'⟩ := exists_dirichletSin_atTop χ
  obtain ⟨c, hc⟩ := hO.bound
  obtain ⟨c', hc'⟩ := hO'.bound
  obtain ⟨x₀, hx₀⟩ := (eventually_atTop.mp hc)
  obtain ⟨y₀, hy₀⟩ := (eventually_atTop.mp hc')
  obtain ⟨CB, hCB0, hCB⟩ := exists_exp_three_half_mul_exp_neg_exp_le hp B
  obtain ⟨CB', hCB'0, hCB'⟩ := exists_exp_three_half_mul_exp_neg_exp_le hp' B
  set u₁ := max 0 (Real.log (max x₀ 1) / 2) with hu₁
  set u₂ := min 0 (-(Real.log (max y₀ 1) / 2)) with hu₂
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := u₂) (b := u₁)).exists_bound_of_continuousOn
    (continuous_dirichletOddAxisKernel χ).continuousOn
  set U := max |u₁| |u₂| with hU
  refine ⟨max (max (max c 0 * CB) (max c' 0 * CB')) (max M 0 * Real.exp (B * U)),
    by positivity, fun u => ?_⟩
  by_cases h1 : u₁ ≤ u
  · have hu0 : 0 ≤ u := le_trans (le_max_left _ _) h1
    have hx : x₀ ≤ Real.exp (2 * u) := by
      have : Real.log (max x₀ 1) ≤ 2 * u := by
        have := le_trans (le_max_right _ _) h1; linarith
      calc x₀ ≤ max x₀ 1 := le_max_left _ _
        _ = Real.exp (Real.log (max x₀ 1)) := (Real.exp_log (by positivity)).symm
        _ ≤ Real.exp (2 * u) := Real.exp_le_exp.mpr this
    have hK := hx₀ _ hx
    rw [Real.norm_of_nonneg (Real.exp_pos _).le] at hK
    unfold dirichletOddAxisKernel
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, abs_of_nonneg hu0]
    calc Real.exp (3 * u / 2) * ‖dirichletOddThetaKernel χ (Real.exp (2 * u))‖
        ≤ Real.exp (3 * u / 2) * (max c 0 * Real.exp (-p * Real.exp (2 * u))) := by
          gcongr; exact hK.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
      _ = max c 0 * (Real.exp (3 * u / 2) * Real.exp (-(p * Real.exp (2 * u)))) := by ring_nf
      _ ≤ max c 0 * (CB * Real.exp (-(B * u))) :=
          mul_le_mul_of_nonneg_left (hCB u hu0) (le_max_right _ _)
      _ ≤ _ := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right (le_trans (le_max_left _ _) (le_max_left _ _))
            (Real.exp_pos _).le
  by_cases h2 : u ≤ u₂
  · have hu0 : u ≤ 0 := le_trans h2 (min_le_left _ _)
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
    unfold dirichletOddAxisKernel
    rw [dirichletOddThetaKernel_eq_sin, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le, abs_of_nonpos hu0]
    have hrpow : Real.exp (2 * u) ^ (3 / 2 : ℝ) = Real.exp (3 * u) := by
      rw [← Real.exp_mul]; ring_nf
    rw [hrpow, Real.norm_of_nonneg (by positivity)]
    have hexp : Real.exp (3 * u / 2) * (1 / Real.exp (3 * u)) = Real.exp (3 * v / 2) := by
      rw [one_div, ← Real.exp_neg, ← Real.exp_add, hv]; ring_nf
    have hey : 1 / Real.exp (2 * u) = Real.exp (2 * v) := by
      rw [hv, one_div, ← Real.exp_neg]; ring_nf
    calc Real.exp (3 * u / 2) * (1 / Real.exp (3 * u) *
          ‖∑ j : ZMod q, χ j * (sinKernel (ZMod.toAddCircle j) (1 / Real.exp (2 * u)) : ℂ)‖)
        ≤ Real.exp (3 * u / 2) * (1 / Real.exp (3 * u) *
            (max c' 0 * Real.exp (-p' * (1 / Real.exp (2 * u))))) := by
          gcongr
          exact hK.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
      _ = max c' 0 * (Real.exp (3 * v / 2) * Real.exp (-(p' * Real.exp (2 * v)))) := by
          rw [← hexp, hey]; ring_nf
      _ ≤ max c' 0 * (CB' * Real.exp (-(B * v))) :=
          mul_le_mul_of_nonneg_left (hCB' v hv0) (le_max_right _ _)
      _ ≤ _ := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right (le_trans (le_max_right _ _) (le_max_left _ _))
            (Real.exp_pos _).le
  · push Not at h1 h2
    have hmem : u ∈ Icc u₂ u₁ := ⟨h2.le, h1.le⟩
    have hb := hM u hmem
    have habs : |u| ≤ U := by
      rw [abs_le]; constructor
      · have := le_max_right |u₁| |u₂|; have := neg_abs_le u₂; linarith [h2]
      · have := le_max_left |u₁| |u₂|; have := le_abs_self u₁; linarith [h1]
    have hexp : 1 ≤ Real.exp (B * U) * Real.exp (-(B * |u|)) := by
      rw [← Real.exp_add]; exact Real.one_le_exp (by nlinarith)
    calc ‖dirichletOddAxisKernel χ u‖ ≤ max M 0 := hb.trans (le_max_left _ _)
      _ ≤ max M 0 * (Real.exp (B * U) * Real.exp (-(B * |u|))) := le_mul_of_one_le_right
          (le_max_right _ _) hexp
      _ = max M 0 * Real.exp (B * U) * Real.exp (-(B * |u|)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le

theorem superExpDecay_dirichletOddAxisKernel (χ : DirichletCharacter ℂ q) :
    SuperExpDecay (dirichletOddAxisKernel χ) := by
  refine ⟨continuous_dirichletOddAxisKernel χ, fun c => ?_⟩
  obtain ⟨C, hC0, hC⟩ := exists_norm_dirichletOddAxisKernel_le χ (B := |c| + 1) (by positivity)
  refine Integrable.mono' ((integrable_exp_neg_mul_abs_modSource (a := 1) one_pos).const_mul C)
    ((continuous_dirichletOddAxisKernel χ).norm.mul (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ‖dirichletOddAxisKernel χ u‖ * Real.exp (c * |u|)
      ≤ C * Real.exp (-((|c| + 1) * |u|)) * Real.exp (c * |u|) :=
        mul_le_mul_of_nonneg_right (hC u) (Real.exp_pos _).le
    _ = C * Real.exp (-((|c| + 1) * |u|) + c * |u|) := by rw [mul_assoc, ← Real.exp_add]
    _ ≤ C * Real.exp (-1 * |u|) := by
        gcongr
        nlinarith [le_abs_self c, abs_nonneg u]

/-! ### The transform of the odd axis kernel -/

theorem hurwitzOddFEPair_hasMellin (a : UnitAddCircle) {w : ℂ} (hw : 3 / 2 < w.re) :
    HasMellin (fun x : ℝ => (oddKernel a x : ℂ)) w ((hurwitzOddFEPair a).Λ w) := by
  have h := (hurwitzOddFEPair a).hasMellin (s := w) (by simpa [hurwitzOddFEPair] using hw)
  have hf : (fun x => (hurwitzOddFEPair a).f x - (hurwitzOddFEPair a).f₀) =
      fun x : ℝ => (oddKernel a x : ℂ) := by
    funext x; simp [hurwitzOddFEPair]
  rwa [hf] at h

/-- On `Re s > 2` the transform of the odd axis kernel is `q^s Λ(s, χ)`. -/
theorem paperFT_dirichletOddAxisKernel_of_re {χ : DirichletCharacter ℂ q}
    (hodd : χ.Odd) {z : ℂ} (hz : 2 < (1 / 2 + I * z).re) :
    paperFT (dirichletOddAxisKernel χ) z = (q : ℂ) ^ (1 / 2 + I * z) *
      DirichletCharacter.completedLFunction χ (1 / 2 + I * z) := by
  set s := 1 / 2 + I * z with hs
  have hw : 3 / 2 < ((s + 1) / 2).re := by
    have : ((s + 1) / 2).re = (s.re + 1) / 2 := by simp
    rw [this]; linarith
  have h1 : paperFT (dirichletOddAxisKernel χ) z =
      (1 / 2) * mellin (dirichletOddThetaKernel χ) ((s + 1) / 2) := by
    rw [← integral_cexp_mul_comp_exp_two]
    unfold paperFT dirichletOddAxisKernel
    congr 1; funext u
    rw [mul_comm ((Real.exp (3 * u / 2) : ℂ)) _, mul_assoc, mul_comm]
    congr 1
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1; rw [hs]; push_cast; ring
  have h2 : mellin (dirichletOddThetaKernel χ) ((s + 1) / 2) =
      ∑ j : ZMod q, χ j * (2 * completedHurwitzZetaOdd (ZMod.toAddCircle j) s) := by
    unfold mellin dirichletOddThetaKernel
    have hint : ∀ j ∈ (Finset.univ : Finset (ZMod q)), IntegrableOn (fun t : ℝ =>
        (t : ℂ) ^ ((s + 1) / 2 - 1) • (χ j * (oddKernel (ZMod.toAddCircle j) t : ℂ))) (Ioi 0) := by
      intro j _
      have h' : IntegrableOn (fun t : ℝ => χ j * ((t : ℂ) ^ ((s + 1) / 2 - 1) •
          (oddKernel (ZMod.toAddCircle j) t : ℂ))) (Ioi 0) :=
        ((hurwitzOddFEPair_hasMellin (ZMod.toAddCircle j) hw).1).const_mul (χ j)
      refine h'.congr_fun (fun t _ => ?_) measurableSet_Ioi
      simp only [smul_eq_mul]; ring
    simp only [Finset.smul_sum]
    rw [integral_finsetSum _ hint]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hm := (hurwitzOddFEPair_hasMellin (ZMod.toAddCircle j) hw).2
    unfold mellin at hm
    rw [show (fun t : ℝ => (t : ℂ) ^ ((s + 1) / 2 - 1) •
        (χ j * (oddKernel (ZMod.toAddCircle j) t : ℂ)))
      = fun t : ℝ => χ j * ((t : ℂ) ^ ((s + 1) / 2 - 1) • (oddKernel (ZMod.toAddCircle j) t : ℂ)) by
        funext t; simp only [smul_eq_mul]; ring,
      integral_const_mul, hm]
    unfold completedHurwitzZetaOdd
    ring
  have h3 : ∑ j : ZMod q, χ j * (2 * completedHurwitzZetaOdd (ZMod.toAddCircle j) s) =
      2 * ((q : ℂ) ^ s * DirichletCharacter.completedLFunction χ s) := by
    have hdef := ZMod.completedLFunction_def_odd hodd.to_fun s
    have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
    unfold DirichletCharacter.completedLFunction
    rw [hdef]
    have hh : (q : ℂ) ^ s * (q : ℂ) ^ (-s) = 1 := by
      rw [← Complex.cpow_add _ _ hq0, add_neg_cancel, Complex.cpow_zero]
    calc ∑ j : ZMod q, χ j * (2 * completedHurwitzZetaOdd (ZMod.toAddCircle j) s)
        = 2 * ∑ j : ZMod q, χ j * completedHurwitzZetaOdd (ZMod.toAddCircle j) s := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      _ = 2 * (((q : ℂ) ^ s * (q : ℂ) ^ (-s)) *
            ∑ j : ZMod q, χ j * completedHurwitzZetaOdd (ZMod.toAddCircle j) s) := by
          rw [hh, one_mul]
      _ = _ := by ring
  rw [h1, h2, h3]; ring

omit [NeZero q] in
/-- An odd character is not trivial. -/
theorem ne_one_of_odd {χ : DirichletCharacter ℂ q} (hodd : χ.Odd) : χ ≠ 1 := by
  rintro rfl
  have h := hodd
  unfold DirichletCharacter.Odd at h
  rw [MulChar.one_apply (isUnit_neg_one)] at h
  norm_num at h

/-- **The odd axis kernel lies in the radical of `L(s, χ)`**: its transform is `q^s Λ(s, χ)`,
`s = 1/2 + iz`, for every `z`. -/
theorem paperFT_dirichletOddAxisKernel {χ : DirichletCharacter ℂ q} (hodd : χ.Odd) (z : ℂ) :
    paperFT (dirichletOddAxisKernel χ) z = (q : ℂ) ^ (1 / 2 + I * z) *
      DirichletCharacter.completedLFunction χ (1 / 2 + I * z) := by
  have hχ := ne_one_of_odd hodd
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
  have hF : Differentiable ℂ (paperFT (dirichletOddAxisKernel χ)) :=
    (superExpDecay_dirichletOddAxisKernel χ).differentiable_paperFT
  have hanF : AnalyticOnNhd ℂ (paperFT (dirichletOddAxisKernel χ)) univ :=
    fun w _ => hF.analyticAt w
  have hanG : AnalyticOnNhd ℂ G univ := fun w _ => hGd.analyticAt w
  set w₀ : ℂ := -(2 * I) with hw₀
  have hopen : IsOpen {w : ℂ | 2 < (1 / 2 + I * w).re} :=
    isOpen_lt continuous_const (Complex.continuous_re.comp (by fun_prop))
  have hw₀mem : 2 < (1 / 2 + I * w₀).re := by
    rw [hw₀]; simp
  have hev : paperFT (dirichletOddAxisKernel χ) =ᶠ[𝓝 w₀] G :=
    Filter.eventually_of_mem (hopen.mem_nhds hw₀mem) fun w hw =>
      paperFT_dirichletOddAxisKernel_of_re hodd hw
  exact hanF.eqOn_of_preconnected_of_eventuallyEq hanG isPreconnected_univ (mem_univ _) hev
    (mem_univ z)

/-- The transform vanishes at every nontrivial zero of `L(s, χ)`. -/
theorem paperFT_dirichletOddAxisKernel_gammaOf_eq_zero (hq : 1 < q) {χ : DirichletCharacter ℂ q}
    (hodd : χ.Odd) {ρ : ℂ} (hρ : Zeta23.ThmE.IsNontrivialZeroL χ ρ) :
    paperFT (dirichletOddAxisKernel χ) (gammaOf ρ) = 0 := by
  rw [paperFT_dirichletOddAxisKernel hodd, half_add_I_mul_gammaOf]
  have hL := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ ρ
    (Or.inr (by omega))
  rw [hρ.1, hodd.gammaFactor_def] at hL
  have hΓ : (ρ + 1).Gammaℝ ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith [hρ.2.1])
  have : DirichletCharacter.completedLFunction χ ρ = 0 := by
    rcases (div_eq_zero_iff.mp hL.symm) with h | h
    · exact h
    · exact absurd h hΓ
  rw [this, mul_zero]

/-- The transform does not vanish at `z = -3i/4` (`s = 5/4`). -/
theorem paperFT_dirichletOddAxisKernel_ne_zero (hq : 1 < q) {χ : DirichletCharacter ℂ q}
    (hodd : χ.Odd) : paperFT (dirichletOddAxisKernel χ) (-(3 / 4 * I)) ≠ 0 := by
  rw [paperFT_dirichletOddAxisKernel hodd]
  have hz : 1 / 2 + I * -(3 / 4 * I) = (5 / 4 : ℂ) := by ring_nf; rw [Complex.I_sq]; ring
  rw [hz]
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  refine mul_ne_zero (by rw [Ne, Complex.cpow_eq_zero_iff]; tauto) ?_
  intro h
  have hL := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ (5 / 4)
    (Or.inr (by omega))
  rw [h, zero_div] at hL
  exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl (ne_one_of_odd hodd))
    (by norm_num) hL

end RHTower
