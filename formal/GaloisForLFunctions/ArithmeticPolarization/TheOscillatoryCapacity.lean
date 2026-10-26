import GaloisForLFunctions.RHTower.WeilPositivityConductorObstruction
import GaloisForLFunctions.RHTower.IsolatedDeepZeroWeilDetection
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.PositivityBeyondIsotropyDoesNotLocalize
import GaloisForLFunctions.ArithmeticPolarization.TwistedSectorsCollideQuartets

/-!
# The oscillatory capacity

What pays the zeros of `ζ` itself? Every pair of points on the local form satisfies the
polarization identity `2 Re(u v̄) = |u|² + |v|² − |u − v|²`. Summed over a zero configuration it
splits Weil's form into two positive pieces of different nature.

* **The capacity decomposition** (`re_W_eq_collided_sub_defect`): for every configuration and every
  test with square-summable transforms on the zeros,
  `Re W(f, f) = D(f) − Δ(f)`, where the **collided form** `D(f) = Σ_ρ m_ρ |f̂(ρ)|²` pairs each zero
  with its conjugate (a determinant, positive) and the **off-line defect**
  `Δ(f) = Σ_ρ (m_ρ/2) |f̂(ρ) − f̂(1 − ρ̄)|²` vanishes on critical zeros. Each off-line pair contributes
  `m |f̂(ρ) − f̂(ρ*)|²` whatever its depth: `Δ` is a capacity for intrinsic charge, uniform in the
  depth, and `Re W ≤ D` always (`re_W_le_collided`).
* **Critical configurations have no defect** (`offLineDefect_eq_zero_of_critical`); a test that
  separates an off-line point from its reflection has positive defect (`offLineDefect_pos`).
* **For `ζ`** (`zeta_summable_collided`, `riemannHypothesis_iff_W_eq_collided`): the decomposition
  holds for every `C²` compactly supported test, and RH holds iff Weil's form equals the collided
  form on every real test. Weil positivity is the inequality `Δ ≤ D` between the off-line capacity
  and the collided mass.

The collided form is a sum of `|f̂(ρ)|²` over the zeros: it is not of the form `Σ_ρ H(ρ)` with `H`
holomorphic, so the explicit formula does not compute it. Computing the capacity is the global
collision problem (`TheCollisionLaw`), which has no meromorphic carrier.
-/

open Complex Filter Topology Set
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticPolarization

open Zeta23

section Capacity

variable (Z : Zeta23.ZeroConfig)

/-- The reflection `ρ ↦ 1 − ρ̄` as an involution of the carrier. -/
def reflEquiv : Z.carrier ≃ Z.carrier where
  toFun ρ := ⟨rosatiRefl ρ, Z.reflect_mem ρ ρ.2⟩
  invFun ρ := ⟨rosatiRefl ρ, Z.reflect_mem ρ ρ.2⟩
  left_inv ρ := by simp [rosatiRefl_rosatiRefl]
  right_inv ρ := by simp [rosatiRefl_rosatiRefl]

/-- The **collided form** `D(f) = Σ_ρ m_ρ |f̂(ρ)|²`. -/
def collidedForm (f : ℝ → ℂ) : ℝ := ∑' ρ : Z.carrier, (Z.mult ρ : ℝ) * Complex.normSq (tr f ρ)

/-- The **off-line defect** `Δ(f) = Σ_ρ (m_ρ/2) |f̂(ρ) − f̂(1 − ρ̄)|²`. -/
def offLineDefect (f : ℝ → ℂ) : ℝ :=
  ∑' ρ : Z.carrier, (Z.mult ρ : ℝ) / 2 * Complex.normSq (tr f ρ - tr f (rosatiRefl ρ))

variable {Z}

theorem collidedForm_nonneg (f : ℝ → ℂ) : 0 ≤ collidedForm Z f :=
  tsum_nonneg fun _ => mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)

theorem offLineDefect_nonneg (f : ℝ → ℂ) : 0 ≤ offLineDefect Z f :=
  tsum_nonneg fun ρ => mul_nonneg (by positivity) (Complex.normSq_nonneg _)

/-- The polarization identity at one pair. -/
theorem re_mul_conj_eq (u v : ℂ) :
    (u * conj v).re = (Complex.normSq u + Complex.normSq v - Complex.normSq (u - v)) / 2 := by
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.sub_re, Complex.sub_im]
  ring

/-- The multiplicity is reflection invariant on the carrier. -/
theorem mult_reflEquiv (ρ : Z.carrier) : Z.mult (reflEquiv Z ρ) = Z.mult ρ :=
  Z.mult_reflect ρ ρ.2

/-- **The capacity decomposition** `Re W = D − Δ`. -/
theorem re_W_eq_collided_sub_defect {f : ℝ → ℂ}
    (hs : Summable fun ρ : Z.carrier => (Z.mult ρ : ℝ) * Complex.normSq (tr f ρ)) :
    (Z.W f f).re = collidedForm Z f - offLineDefect Z f := by
  set a : Z.carrier → ℝ := fun ρ => (Z.mult ρ : ℝ) * Complex.normSq (tr f ρ)
  set b : Z.carrier → ℝ := fun ρ => (Z.mult ρ : ℝ) * Complex.normSq (tr f (rosatiRefl ρ))
  set c : Z.carrier → ℝ := fun ρ =>
    (Z.mult ρ : ℝ) / 2 * Complex.normSq (tr f ρ - tr f (rosatiRefl ρ))
  have hb_eq : b = a ∘ reflEquiv Z := by
    funext ρ
    simp only [b, a, Function.comp, mult_reflEquiv]
    rfl
  have hbs : Summable b := by rw [hb_eq]; exact (reflEquiv Z).summable_iff.mpr hs
  have hcs : Summable c := by
    refine Summable.of_nonneg_of_le (fun ρ => mul_nonneg (by positivity) (Complex.normSq_nonneg _))
      (fun ρ => ?_) (hs.add hbs)
    have hm : (0 : ℝ) ≤ Z.mult ρ := Nat.cast_nonneg _
    have key : Complex.normSq (tr f ρ - tr f (rosatiRefl ρ)) ≤
        2 * (Complex.normSq (tr f ρ) + Complex.normSq (tr f (rosatiRefl ρ))) := by
      have := re_mul_conj_eq (tr f ρ) (tr f (rosatiRefl ρ))
      have h2 := Complex.abs_re_le_norm (tr f ρ * conj (tr f (rosatiRefl ρ)))
      rw [norm_mul, Complex.norm_conj] at h2
      have hn1 := Complex.normSq_eq_norm_sq (tr f ρ)
      have hn2 := Complex.normSq_eq_norm_sq (tr f (rosatiRefl ρ))
      nlinarith [abs_le.mp h2, sq_nonneg (‖tr f ρ‖ - ‖tr f (rosatiRefl ρ)‖)]
    simp only [c, a, b]
    nlinarith
  -- the summand identity
  have hterm : ∀ ρ : Z.carrier, (Z.Wsummand f f ρ).re = (a ρ + b ρ) / 2 - c ρ := by
    intro ρ
    rw [Zeta23.ZeroConfig.Wsummand, paperFT_conj_gammaOf, ← tr, mul_assoc, ← Complex.ofReal_natCast,
      Complex.re_ofReal_mul, re_mul_conj_eq]
    simp only [a, b, c]
    ring
  have hWs : Summable fun ρ : Z.carrier => Z.Wsummand f f ρ := by
    refine Summable.of_norm_bounded (g := fun ρ => (a ρ + b ρ) / 2) ((hs.add hbs).div_const 2)
      fun ρ => ?_
    rw [Zeta23.ZeroConfig.Wsummand, paperFT_conj_gammaOf, ← tr, norm_mul, norm_mul,
      Complex.norm_conj, Complex.norm_natCast]
    simp only [a, b]
    have hn1 := Complex.normSq_eq_norm_sq (tr f ρ)
    have hn2 := Complex.normSq_eq_norm_sq (tr f (rosatiRefl ρ))
    have hm : (0 : ℝ) ≤ Z.mult ρ := Nat.cast_nonneg _
    nlinarith [sq_nonneg (‖tr f ρ‖ - ‖tr f (rosatiRefl ρ)‖), norm_nonneg (tr f ρ),
      norm_nonneg (tr f (rosatiRefl ρ)), mul_nonneg hm (sq_nonneg (‖tr f ρ‖ - ‖tr f (rosatiRefl ρ)‖))]
  have hre : (Z.W f f).re = ∑' ρ : Z.carrier, (Z.Wsummand f f ρ).re := by
    rw [Zeta23.ZeroConfig.W]
    exact Complex.reCLM.map_tsum hWs
  have hbsum : ∑' ρ, b ρ = ∑' ρ, a ρ := by
    rw [hb_eq]; exact (reflEquiv Z).tsum_eq a
  rw [hre, tsum_congr hterm, (((hs.add hbs).div_const 2)).tsum_sub hcs, tsum_div_const,
    hs.tsum_add hbs, hbsum]
  simp only [collidedForm, offLineDefect, a, c]
  ring

/-- **Weil's form is dominated by the collided form.** -/
theorem re_W_le_collided {f : ℝ → ℂ}
    (hs : Summable fun ρ : Z.carrier => (Z.mult ρ : ℝ) * Complex.normSq (tr f ρ)) :
    (Z.W f f).re ≤ collidedForm Z f := by
  rw [re_W_eq_collided_sub_defect hs]; linarith [offLineDefect_nonneg (Z := Z) f]

/-- **Critical configurations have no defect.** -/
theorem offLineDefect_eq_zero_of_critical (hcrit : ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2) (f : ℝ → ℂ) :
    offLineDefect Z f = 0 := by
  rw [offLineDefect]
  refine (tsum_congr fun ρ => ?_).trans tsum_zero
  rw [(rosatiRefl_eq_self_iff ρ).mpr (hcrit ρ ρ.2), sub_self, map_zero, mul_zero]

/-- **A separating test has positive defect.** -/
theorem offLineDefect_pos {f : ℝ → ℂ}
    (hs : Summable fun ρ : Z.carrier => (Z.mult ρ : ℝ) * Complex.normSq (tr f ρ))
    {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier) (hsep : tr f ρ₀ ≠ tr f (rosatiRefl ρ₀)) :
    0 < offLineDefect Z f := by
  -- summability of the defect, as in the decomposition
  have hbs : Summable fun ρ : Z.carrier =>
      (Z.mult ρ : ℝ) * Complex.normSq (tr f (rosatiRefl ρ)) := by
    have : (fun ρ : Z.carrier => (Z.mult ρ : ℝ) * Complex.normSq (tr f (rosatiRefl ρ))) =
        (fun ρ : Z.carrier => (Z.mult ρ : ℝ) * Complex.normSq (tr f ρ)) ∘ reflEquiv Z := by
      funext ρ; simp only [Function.comp, mult_reflEquiv]; rfl
    rw [this]; exact (reflEquiv Z).summable_iff.mpr hs
  have hcs : Summable fun ρ : Z.carrier =>
      (Z.mult ρ : ℝ) / 2 * Complex.normSq (tr f ρ - tr f (rosatiRefl ρ)) := by
    refine Summable.of_nonneg_of_le (fun ρ => mul_nonneg (by positivity) (Complex.normSq_nonneg _))
      (fun ρ => ?_) (hs.add hbs)
    have key : Complex.normSq (tr f ρ - tr f (rosatiRefl ρ)) ≤
        2 * (Complex.normSq (tr f ρ) + Complex.normSq (tr f (rosatiRefl ρ))) := by
      have h2 := Complex.abs_re_le_norm (tr f ρ * conj (tr f (rosatiRefl ρ)))
      rw [norm_mul, Complex.norm_conj] at h2
      have := re_mul_conj_eq (tr f ρ) (tr f (rosatiRefl ρ))
      have hn1 := Complex.normSq_eq_norm_sq (tr f ρ)
      have hn2 := Complex.normSq_eq_norm_sq (tr f (rosatiRefl ρ))
      nlinarith [abs_le.mp h2, sq_nonneg (‖tr f ρ‖ - ‖tr f (rosatiRefl ρ)‖)]
    have hm : (0 : ℝ) ≤ Z.mult ρ := Nat.cast_nonneg _
    nlinarith
  refine hcs.tsum_pos (fun ρ => mul_nonneg (by positivity) (Complex.normSq_nonneg _))
    ⟨ρ₀, hρ₀⟩ ?_
  have hm : (1 : ℝ) ≤ Z.mult ρ₀ := by exact_mod_cast Z.one_le_mult ρ₀ hρ₀
  have hn : 0 < Complex.normSq (tr f ρ₀ - tr f (rosatiRefl ρ₀)) :=
    Complex.normSq_pos.mpr (sub_ne_zero.mpr hsep)
  exact mul_pos (by linarith) hn

end Capacity

/-! ### The capacity of `ζ` -/

/-- **The collided form of `ζ` converges** for every `C²` compactly supported test. -/
theorem zeta_summable_collided {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    Summable fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) * Complex.normSq (tr f ρ) := by
  obtain ⟨R, hR⟩ := hfc.isCompact.isBounded.subset_closedBall 0
  set a := max R 0
  have hsupp : ∀ u, f u ≠ 0 → |u| ≤ a := by
    intro u hu
    have : u ∈ Metric.closedBall (0 : ℝ) R := hR (subset_tsupport f hu)
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  set B := 4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)
  refine Summable.of_nonneg_of_le (fun ρ => mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _))
    (fun ρ => ?_) (RHTower.summable_zetaZeroConfig.mul_left (5 / 4 * (Real.exp a * B ^ 2)))
  have hstrip := zetaZeroConfig.strip ρ ρ.2
  have hdec := RHTower.norm_paperFT_le_decay hf hsupp (gammaOf ρ)
  have him : |(gammaOf (ρ : ℂ)).im| ≤ 1 / 2 := by
    rw [gammaOf, Complex.div_I]
    simp only [Complex.neg_im, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.I_re,
      Complex.I_im]
    norm_num
    rw [abs_le]; constructor <;> linarith [hstrip.1, hstrip.2]
  have hre_g : (gammaOf (ρ : ℂ)).re = (ρ : ℂ).im := by
    rw [gammaOf, Complex.div_I]; simp
  have hnorm_g : Complex.normSq (gammaOf (ρ : ℂ)) ≤ (ρ : ℂ).im ^ 2 + 1 / 4 := by
    rw [Complex.normSq_apply, ← hre_g]
    have := abs_le.mp him
    nlinarith
  have hB0 : 0 ≤ B := by
    have : 0 ≤ (∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖ :=
      add_nonneg (MeasureTheory.integral_nonneg fun _ => norm_nonneg _)
        (MeasureTheory.integral_nonneg fun _ => norm_nonneg _)
    positivity
  have hexp : Real.exp (|(gammaOf (ρ : ℂ)).im| * a) ≤ Real.exp (a / 2) :=
    Real.exp_le_exp.mpr (by nlinarith [le_max_right R 0, abs_nonneg (gammaOf (ρ : ℂ)).im])
  set y := (ρ : ℂ).im
  have hden : 0 < 1 + |y| := by positivity
  have htr : ‖tr f ρ‖ ≤ Real.exp (a / 2) * B / (1 + |y|) ^ 2 := by
    rw [tr]
    refine hdec.trans ?_
    rw [hre_g]
    gcongr
  have htr2 : Complex.normSq (tr f ρ) ≤ (Real.exp a * B ^ 2) / (1 + |y|) ^ 4 := by
    rw [Complex.normSq_eq_norm_sq]
    have h0 := norm_nonneg (tr f ρ)
    calc ‖tr f ρ‖ ^ 2 ≤ (Real.exp (a / 2) * B / (1 + |y|) ^ 2) ^ 2 := by gcongr
      _ = (Real.exp a * B ^ 2) / (1 + |y|) ^ 4 := by
        rw [div_pow, mul_pow, ← Real.exp_nat_mul]; push_cast; ring_nf
  have hpow : (4 / 5) * (1 + Complex.normSq (gammaOf (ρ : ℂ))) ≤ (1 + |y|) ^ 4 := by
    have h1 : (1 + |y|) ^ 2 ≤ (1 + |y|) ^ 4 := by
      have : 1 ≤ (1 + |y|) ^ 2 := by nlinarith [abs_nonneg y]
      nlinarith
    nlinarith [sq_abs y, abs_nonneg y]
  have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
  have hq : 0 < 1 + Complex.normSq (gammaOf (ρ : ℂ)) := by
    have := Complex.normSq_nonneg (gammaOf (ρ : ℂ)); linarith
  have hE : 0 ≤ Real.exp a * B ^ 2 := by positivity
  calc (zetaZeroConfig.mult ρ : ℝ) * Complex.normSq (tr f ρ)
      ≤ (zetaZeroConfig.mult ρ : ℝ) * ((Real.exp a * B ^ 2) / (1 + |y|) ^ 4) :=
        mul_le_mul_of_nonneg_left htr2 hm
    _ ≤ (zetaZeroConfig.mult ρ : ℝ) *
          ((Real.exp a * B ^ 2) / ((4 / 5) * (1 + Complex.normSq (gammaOf (ρ : ℂ))))) := by
        gcongr
    _ = 5 / 4 * (Real.exp a * B ^ 2) *
          ((zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf (ρ : ℂ)))) := by
        field_simp

/-- The transform `tr` of a real test is the corpus `mellinAt`. -/
theorem tr_cx_eq_mellinAt (g : ℝ → ℝ) (s : ℂ) :
    tr (fun u => (g u : ℂ)) s = ArithmeticCorrespondencePositivity.mellinAt g s := by
  rw [tr_eq, ArithmeticCorrespondencePositivity.mellinAt]

/-- **RH is the equality of Weil's form with the collided form** on every `C²` compactly supported
real test. -/
theorem riemannHypothesis_iff_W_eq_collided :
    RiemannHypothesis ↔
      ∀ g : ℝ → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
        (zetaZeroConfig.W (fun u => (g u : ℂ)) (fun u => (g u : ℂ))).re =
          collidedForm zetaZeroConfig (fun u => (g u : ℂ)) := by
  have hcx : ∀ {g : ℝ → ℝ}, ContDiff ℝ 2 g → ContDiff ℝ 2 (fun u => (g u : ℂ)) :=
    fun hg => Complex.ofRealCLM.contDiff.comp hg
  have hcxc : ∀ {g : ℝ → ℝ}, HasCompactSupport g → HasCompactSupport (fun u => (g u : ℂ)) :=
    fun hg => hg.comp_left Complex.ofReal_zero
  constructor
  · intro hRH g hg hgc
    have hcrit : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re = 1 / 2 := by
      intro ρ hρ
      rw [zetaZeroConfig_carrier] at hρ
      exact hRH ρ hρ.1 (fun ⟨n, hn⟩ => by
        have := hρ.2.1; rw [hn] at this; simp at this; linarith [(by positivity : (0 : ℝ) ≤ n)])
        (fun h1 => by rw [h1] at hρ; exact absurd hρ.2.2 (by norm_num))
    rw [re_W_eq_collided_sub_defect (zeta_summable_collided (hcx hg) (hcxc hgc)),
      offLineDefect_eq_zero_of_critical hcrit, sub_zero]
  · intro h
    rw [RHTower.riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip]
    intro s hs1 hs2 hz
    have hmem : s ∈ zetaZeroConfig.carrier := by
      rw [zetaZeroConfig_carrier]; exact ⟨hz, by linarith, hs2⟩
    -- a real test seeing `s`, and its translate
    obtain ⟨⟨⟨g, hgreal⟩, _hgsupp⟩, hg0, -⟩ :=
      ArithmeticCorrespondencePositivity.exists_mem_realTestsAt_mellinAt_ne_zero one_pos s s
    have hg2 : ContDiff ℝ 2 g := hgreal.1
    have hgc : HasCompactSupport g := hgreal.2
    have hne : s.re ≠ 1 / 2 := by linarith
    -- one of `g`, `g(· − 1)` separates `s` from `1 − s̄`
    have hsep : ∃ g' : ℝ → ℝ, ContDiff ℝ 2 g' ∧ HasCompactSupport g' ∧
        tr (fun u => (g' u : ℂ)) s ≠ tr (fun u => (g' u : ℂ)) (rosatiRefl s) := by
      by_cases h0 : tr (fun u => (g u : ℂ)) s = tr (fun u => (g u : ℂ)) (rosatiRefl s)
      · refine ⟨fun u => g (u - 1), hg2.comp (contDiff_id.sub contDiff_const),
          hgc.comp_homeomorph (Homeomorph.subRight 1), ?_⟩
        rw [tr_cx_eq_mellinAt, tr_cx_eq_mellinAt, ArithmeticCorrespondencePositivity.mellinAt_translate,
          ArithmeticCorrespondencePositivity.mellinAt_translate, ← tr_cx_eq_mellinAt,
          ← tr_cx_eq_mellinAt, ← h0]
        intro heq
        have hA : tr (fun u => (g u : ℂ)) s ≠ 0 := by rw [tr_cx_eq_mellinAt]; exact hg0
        have hexp := mul_right_cancel₀ hA heq
        have := congrArg (‖·‖) hexp
        simp only [Complex.norm_exp] at this
        have hre := Real.exp_injective this
        simp [rosatiRefl] at hre
        exact hne (by linarith)
      · exact ⟨g, hg2, hgc, h0⟩
    obtain ⟨g', hg', hgc', hsep'⟩ := hsep
    have hpos := offLineDefect_pos (zeta_summable_collided (hcx hg') (hcxc hgc')) hmem hsep'
    have heq := h g' hg' hgc'
    rw [re_W_eq_collided_sub_defect (zeta_summable_collided (hcx hg') (hcxc hgc'))] at heq
    linarith

end GaloisForLFunctions.ArithmeticPolarization
