import GaloisForLFunctions.RHTower.WeilDilationResidueRealness
import GaloisForLFunctions.RHTower.Zeta23SimpleCriticalDensity

/-!
# Rigidity of dilated von Mangoldt weights under Weil positivity

If the weights `Λ(n) + Σ_{m ∈ S} b(m) Λ(n/m)` (finite `S ⊆ ℕ_{≥1}`, real `b`) are Weil-positive
on polar tests at every level, then `b` vanishes on `S`.

* At every critical zero `½ + iγ` of `ζ` the Dirichlet polynomial `B(s) = Σ b(m) m^{-s}` is real
  (`dilationPoly_im_eq_zero_of_weilPositive`).
* The multiplicative test `g(x) = Σ b(m) (h(mx) − h(x/m)/m)`, with `h` a narrow tent at `1`, is
  continuous with compact support in `(0, ∞)`, and its Mellin transform on the critical line is
  `2i·Im B(½+it)·Mh(½+it)` (`mellin_dilationMellinTest`).  It therefore vanishes at every critical
  zero, and the unconditional superlinear density of simple critical zeros forces `g = 0`
  (`weilTest_eq_zero_of_cofinite_simpleCritical_mellin_zero`).
* The tents are disjoint, so `g(m₀) = −b(m₀) δ / m₀`, which gives `b(m₀) = 0` for `m₀ ≥ 2`.
* The remaining weight `(1 + b(1)) Λ` is rigid by scaling (`scaled_vonMangoldt_weilAtomSymbol_not_nonneg`).
-/

open Complex MeasureTheory Set Filter
open scoped ComplexConjugate ArithmeticFunction

noncomputable section

namespace RHTower

/-- The tent `max 0 (δ − |x − 1|)` of half-width `δ` centred at `1`. -/
def unitTent (δ x : ℝ) : ℝ := max 0 (δ - |x - 1|)

theorem continuous_unitTent (δ : ℝ) : Continuous (unitTent δ) :=
  continuous_const.max (continuous_const.sub ((continuous_id.sub continuous_const).abs))

theorem unitTent_eq_zero {δ x : ℝ} (h : δ ≤ |x - 1|) : unitTent δ x = 0 :=
  max_eq_left (by linarith)

theorem abs_sub_one_lt_of_unitTent_ne_zero {δ x : ℝ} (h : unitTent δ x ≠ 0) : |x - 1| < δ := by
  by_contra h'
  exact h (unitTent_eq_zero (not_lt.mp h'))

theorem unitTent_one {δ : ℝ} (hδ : 0 ≤ δ) : unitTent δ 1 = δ := by
  simp [unitTent, hδ]

/-- A continuous function supported in a compact interval of `(0, ∞)` is Mellin convergent at
every `s`. -/
theorem mellinConvergent_of_support_Icc {f : ℝ → ℂ} (hf : Continuous f) {c d : ℝ} (hc : 0 < c)
    (hsupp : Function.support f ⊆ Icc c d) (s : ℂ) : MellinConvergent f s := by
  unfold MellinConvergent
  have hon : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • f t) (Icc c d) := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le hc ht.1)
    exact ((continuousAt_ofReal_cpow_const t (s - 1) (Or.inr ht0)).smul
      hf.continuousAt).continuousWithinAt
  refine hon.of_forall_sdiff_eq_zero measurableSet_Ioi ?_
  intro x hx
  have hfx : f x = 0 := by
    by_contra h
    exact hx.2 (hsupp h)
  simp [hfx]

theorem mellin_finset_sum_of_convergent {ι : Type*} (T : Finset ι) (F : ι → ℝ → ℂ) {s : ℂ}
    (hF : ∀ i ∈ T, MellinConvergent (F i) s) :
    mellin (fun t => ∑ i ∈ T, F i t) s = ∑ i ∈ T, mellin (F i) s := by
  unfold mellin
  simp_rw [Finset.smul_sum]
  exact integral_finsetSum T hF

theorem mellin_sub_of_convergent {f g : ℝ → ℂ} {s : ℂ} (hf : MellinConvergent f s)
    (hg : MellinConvergent g s) : mellin (fun t => f t - g t) s = mellin f s - mellin g s := by
  unfold mellin
  simp_rw [smul_sub]
  exact integral_sub hf hg

theorem mellinConvergent_unitTent {δ : ℝ} (hδ : δ < 1) (s : ℂ) :
    MellinConvergent (fun x => (unitTent δ x : ℂ)) s := by
  refine mellinConvergent_of_support_Icc (continuous_ofReal.comp (continuous_unitTent δ))
    (c := 1 - δ) (d := 1 + δ) (by linarith) ?_ s
  intro x hx
  have hx' : unitTent δ x ≠ 0 := by
    intro h0; exact hx (by simp [h0])
  have h := abs_sub_one_lt_of_unitTent_ne_zero hx'
  rw [abs_lt] at h
  constructor <;> linarith

/-- The multiplicative test term `b(m) h(mx) − (b(m)/m) h(x/m)` for the tent `h`. -/
def dilationMellinTerm (b : ℕ → ℝ) (δ : ℝ) (m : ℕ) (x : ℝ) : ℂ :=
  (b m : ℂ) * (unitTent δ (m * x) : ℂ) - ((b m / m : ℝ) : ℂ) * (unitTent δ ((m : ℝ)⁻¹ * x) : ℂ)

/-- The multiplicative test `Σ_{m ∈ S} (b(m) h(mx) − (b(m)/m) h(x/m))`. -/
def dilationMellinTest (S : Finset ℕ) (b : ℕ → ℝ) (δ : ℝ) (x : ℝ) : ℂ :=
  ∑ m ∈ S, dilationMellinTerm b δ m x

theorem mellin_dilationMellinTerm {δ : ℝ} (hδ : δ < 1) (b : ℕ → ℝ) {m : ℕ} (hm : 1 ≤ m) (s : ℂ) :
    mellin (dilationMellinTerm b δ m) s =
      (b m : ℂ) * ((m : ℂ) ^ (-s) - (m : ℂ) ^ (s - 1)) *
        mellin (fun x => (unitTent δ x : ℂ)) s := by
  set H : ℝ → ℂ := fun x => (unitTent δ x : ℂ) with hH
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hmi : (0 : ℝ) < (m : ℝ)⁻¹ := inv_pos.mpr hm0
  have hH0 : MellinConvergent H s := mellinConvergent_unitTent hδ s
  have h1 : MellinConvergent (fun t => (b m : ℂ) • H (m * t)) s :=
    ((MellinConvergent.comp_mul_left hm0).2 hH0).const_smul _
  have h2 : MellinConvergent (fun t => ((b m / m : ℝ) : ℂ) • H ((m : ℝ)⁻¹ * t)) s :=
    ((MellinConvergent.comp_mul_left hmi).2 hH0).const_smul _
  have hfun : dilationMellinTerm b δ m =
      fun t => (b m : ℂ) • H (m * t) - ((b m / m : ℝ) : ℂ) • H ((m : ℝ)⁻¹ * t) := by
    funext t; simp [dilationMellinTerm, hH, smul_eq_mul]
  rw [hfun, mellin_sub_of_convergent h1 h2, mellin_const_smul, mellin_const_smul,
    mellin_comp_mul_left H s hm0, mellin_comp_mul_left H s hmi]
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have harg : (m : ℂ).arg ≠ Real.pi := by
    rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm
  have hinv : (((m : ℝ)⁻¹ : ℝ) : ℂ) ^ (-s) = (m : ℂ) ^ s := by
    rw [Complex.ofReal_inv, Complex.ofReal_natCast, Complex.inv_cpow _ _ harg, Complex.cpow_neg,
      inv_inv]
  have hsub : (m : ℂ) ^ (s - 1) = (m : ℂ) ^ s / m := by
    rw [Complex.cpow_sub _ _ hmC, Complex.cpow_one]
  rw [hinv, hsub]
  simp only [smul_eq_mul, Complex.ofReal_natCast, Complex.ofReal_div]
  field_simp

theorem mellinConvergent_dilationMellinTerm {δ : ℝ} (hδ : δ < 1) (b : ℕ → ℝ) {m : ℕ} (hm : 1 ≤ m)
    (s : ℂ) : MellinConvergent (dilationMellinTerm b δ m) s := by
  set H : ℝ → ℂ := fun x => (unitTent δ x : ℂ) with hH
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hmi : (0 : ℝ) < (m : ℝ)⁻¹ := inv_pos.mpr hm0
  have hH0 : MellinConvergent H s := mellinConvergent_unitTent hδ s
  have h1 : MellinConvergent (fun t => (b m : ℂ) • H (m * t)) s :=
    ((MellinConvergent.comp_mul_left hm0).2 hH0).const_smul _
  have h2 : MellinConvergent (fun t => ((b m / m : ℝ) : ℂ) • H ((m : ℝ)⁻¹ * t)) s :=
    ((MellinConvergent.comp_mul_left hmi).2 hH0).const_smul _
  have hfun : dilationMellinTerm b δ m =
      fun t => (b m : ℂ) • H (m * t) - ((b m / m : ℝ) : ℂ) • H ((m : ℝ)⁻¹ * t) := by
    funext t; simp [dilationMellinTerm, hH, smul_eq_mul]
  rw [hfun]
  unfold MellinConvergent at h1 h2 ⊢
  simp_rw [smul_sub]
  exact h1.sub h2

/-- On the critical line, `m^{s−1}` is the conjugate of `m^{−s}`. -/
theorem natCast_cpow_critical_sub_one (m : ℕ) (t : ℝ) :
    (m : ℂ) ^ ((1 / 2 : ℂ) + t * I - 1) = conj ((m : ℂ) ^ (-((1 / 2 : ℂ) + t * I))) := by
  have harg : (m : ℂ).arg ≠ Real.pi := by
    rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm
  have h : (1 / 2 : ℂ) + t * I - 1 = conj (-((1 / 2 : ℂ) + t * I)) := by
    apply Complex.ext <;> simp; norm_num
  rw [h, Complex.cpow_conj _ _ harg, Complex.conj_natCast]

/-- On the critical line the Mellin factor `Σ b(m)(m^{−s} − m^{s−1})` is `2i·Im B(s)`. -/
theorem sum_dilationMellin_factor_critical (S : Finset ℕ) (b : ℕ → ℝ) (t : ℝ) :
    ∑ m ∈ S, (b m : ℂ) * ((m : ℂ) ^ (-((1 / 2 : ℂ) + t * I)) -
        (m : ℂ) ^ ((1 / 2 : ℂ) + t * I - 1)) =
      ((2 * (dilationPoly S b ((1 / 2 : ℂ) + t * I)).im : ℝ) : ℂ) * I := by
  rw [← Complex.sub_conj, dilationPoly, map_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m _
  rw [natCast_cpow_critical_sub_one, map_mul, Complex.conj_ofReal]
  ring

/-- The Mellin transform of the dilation test on the critical line is `2i·Im B(s)·Mh(s)`. -/
theorem mellin_dilationMellinTest {δ : ℝ} (hδ : δ < 1) {S : Finset ℕ} (hS : ∀ m ∈ S, 1 ≤ m)
    (b : ℕ → ℝ) (t : ℝ) :
    mellin (dilationMellinTest S b δ) ((1 / 2 : ℂ) + t * I) =
      ((2 * (dilationPoly S b ((1 / 2 : ℂ) + t * I)).im : ℝ) : ℂ) * I *
        mellin (fun x => (unitTent δ x : ℂ)) ((1 / 2 : ℂ) + t * I) := by
  have hconv : ∀ m ∈ S, MellinConvergent (dilationMellinTerm b δ m) ((1 / 2 : ℂ) + t * I) :=
    fun m hm => mellinConvergent_dilationMellinTerm hδ b (hS m hm) _
  show mellin (fun x => ∑ m ∈ S, dilationMellinTerm b δ m x) _ = _
  rw [mellin_finset_sum_of_convergent S _ hconv,
    Finset.sum_congr rfl (fun m hm => mellin_dilationMellinTerm hδ b (hS m hm) _),
    ← Finset.sum_mul, sum_dilationMellin_factor_critical]

/-- **Weil positivity kills every dilation coefficient beyond `1`.**  If
`Λ(n) + Σ_{m ∈ S} b(m) Λ(n/m)` is Weil-positive, then `b(m) = 0` for every `m ∈ S` with `m ≥ 2`.

The test `g = Σ b(m)(h(mx) − h(x/m)/m)` has critical-line Mellin transform `2i·Im B·Mh`, which
vanishes at every critical zero because `B` is real there; the superlinear density of simple
critical zeros forces `g = 0`, and `g(m₀) = −b(m₀)δ/m₀`. -/
theorem dilation_coeff_eq_zero_of_weilPositive {S : Finset ℕ} (hS : ∀ m ∈ S, 1 ≤ m)
    (b : ℕ → ℝ) (hW : WeilPositive fun n => (Λ n : ℝ) + dilatedVonMangoldt S b n) {m₀ : ℕ}
    (hm₀ : m₀ ∈ S) (h2 : 2 ≤ m₀) : b m₀ = 0 := by
  set N : ℕ := S.sup id with hN
  have hle : ∀ m ∈ S, (m : ℝ) ≤ N := fun m hm => by
    exact_mod_cast (Finset.le_sup (f := id) hm)
  have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  set δ : ℝ := 1 / (2 * ((N : ℝ) + 1)) with hδdef
  have hδ0 : 0 < δ := by positivity
  have hδhalf : δ ≤ 1 / 2 := by
    rw [hδdef, div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  have hδ1 : δ < 1 := by linarith
  have hδm : ∀ m ∈ S, δ * m ≤ 1 / 2 := by
    intro m hm
    have hmN := hle m hm
    rw [hδdef, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  set g : ℝ → ℂ := dilationMellinTest S b δ with hg
  have hgc : Continuous g := by
    refine continuous_finsetSum _ (fun m _ => ?_)
    unfold dilationMellinTerm
    exact (continuous_const.mul (continuous_ofReal.comp ((continuous_unitTent δ).comp
      (continuous_const.mul continuous_id)))).sub
      (continuous_const.mul (continuous_ofReal.comp ((continuous_unitTent δ).comp
      (continuous_const.mul continuous_id))))
  set A : ℝ := 2 * ((N : ℝ) + 1) with hA
  have hA1 : 1 ≤ A := by rw [hA]; have : (0 : ℝ) ≤ N := Nat.cast_nonneg N; linarith
  have hApos : 0 < A := by linarith
  have hexpA : Real.exp (Real.log A) = A := Real.exp_log hApos
  have hexpnA : Real.exp (-Real.log A) = A⁻¹ := by rw [Real.exp_neg, hexpA]
  have hsupp : Function.support g ⊆ Icc (Real.exp (-Real.log A)) (Real.exp (Real.log A)) := by
    intro x hx
    rw [hexpA, hexpnA]
    obtain ⟨m, hm, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hS m hm
    have hmN := hle m hm
    have hmA : (m : ℝ) + 1 ≤ A := by rw [hA]; linarith
    have hδm' := hδm m hm
    have hcases : unitTent δ (m * x) ≠ 0 ∨ unitTent δ ((m : ℝ)⁻¹ * x) ≠ 0 := by
      by_contra hcon
      rw [not_or, not_not, not_not] at hcon
      apply hterm
      simp [dilationMellinTerm, hcon.1, hcon.2]
    rcases hcases with h | h
    · have hab := abs_lt.mp (abs_sub_one_lt_of_unitTent_ne_zero h)
      have hlow : 1 / 2 < (m : ℝ) * x := by linarith [hab.1]
      have hxpos : 0 < x := by
        by_contra hx0
        have hx0' := not_lt.mp hx0
        nlinarith
      constructor
      · rw [inv_le_iff_one_le_mul₀ hApos]; nlinarith
      · nlinarith
    · have hab := abs_lt.mp (abs_sub_one_lt_of_unitTent_ne_zero h)
      have hmpos : (0 : ℝ) < m := by linarith
      have hy : (m : ℝ) * ((m : ℝ)⁻¹ * x) = x := by field_simp
      set y := (m : ℝ)⁻¹ * x with hydef
      have hylow : 1 / 2 < y := by linarith [hab.1]
      have hyhigh : y < 3 / 2 := by linarith [hab.2]
      have hmy : (1 : ℝ) / 2 < m * y := by nlinarith
      have hA2 : (2 : ℝ) ≤ A := by linarith
      constructor
      · rw [inv_le_iff_one_le_mul₀ hApos, ← hy]; nlinarith
      · rw [← hy]; nlinarith
  have hvanish : ∀ t : ℝ, t ∉ (∅ : Finset ℝ) → 0 < t → xi (linePt t) = 0 →
      (analyticOrderAt xi (linePt t)).toNat = 1 →
        mellin g ((1 / 2 : ℂ) + (t : ℂ) * I) = 0 := by
    intro t _ _ hxi _
    have hline : linePt t = (1 / 2 : ℂ) + t * I := by simp [linePt]
    have hre : (linePt t).re = 1 / 2 := by simp [linePt]
    have hz : riemannZeta ((1 / 2 : ℂ) + t * I) = 0 := by
      rw [← hline]
      exact (xi_zero_iff_zeta_zero_of_mem_strip (by rw [hre]; norm_num)
        (by rw [hre]; norm_num)).1 hxi
    have him := dilationPoly_im_eq_zero_of_weilPositive hS b hW hz
    rw [hg, mellin_dilationMellinTest hδ1 hS b t, him]
    simp
  have hg0 := weilTest_eq_zero_of_cofinite_simpleCritical_mellin_zero
    (Real.log_nonneg hA1) g hgc hsupp ∅ hvanish
  have hgm := congrFun hg0 (m₀ : ℝ)
  have hm₀1 : (2 : ℝ) ≤ m₀ := by exact_mod_cast h2
  have hsum : g m₀ = dilationMellinTerm b δ m₀ m₀ := by
    rw [hg]
    unfold dilationMellinTest
    apply Finset.sum_eq_single m₀
    · intro m hm hne
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hS m hm
      have hmpos : (0 : ℝ) < m := by linarith
      have hT1 : unitTent δ (m * m₀) = 0 := by
        apply unitTent_eq_zero
        rw [abs_of_nonneg (by nlinarith)]
        nlinarith
      have hdist : (1 : ℝ) ≤ |(m₀ : ℝ) - m| := by
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have : (m : ℝ) + 1 ≤ m₀ := by exact_mod_cast hlt
          rw [abs_of_nonneg (by linarith)]; linarith
        · have : (m₀ : ℝ) + 1 ≤ m := by exact_mod_cast hgt
          rw [abs_of_nonpos (by linarith)]; linarith
      have hT2 : unitTent δ ((m : ℝ)⁻¹ * m₀) = 0 := by
        apply unitTent_eq_zero
        have heq : (m : ℝ)⁻¹ * m₀ - 1 = ((m₀ : ℝ) - m) / m := by field_simp
        rw [heq, abs_div, abs_of_pos hmpos, le_div_iff₀ hmpos]
        linarith [hδm m hm]
      simp [dilationMellinTerm, hT1, hT2]
    · intro h; exact absurd hm₀ h
  have hm₀pos : (0 : ℝ) < m₀ := by linarith
  have hT1 : unitTent δ (m₀ * m₀) = 0 := by
    apply unitTent_eq_zero
    rw [abs_of_nonneg (by nlinarith)]
    nlinarith
  have hT2 : unitTent δ ((m₀ : ℝ)⁻¹ * m₀) = δ := by
    rw [inv_mul_cancel₀ hm₀pos.ne', unitTent_one hδ0.le]
  rw [hsum] at hgm
  simp only [dilationMellinTerm, hT1, hT2, Pi.zero_apply] at hgm
  push_cast at hgm
  have hC : ((b m₀ / m₀ * δ : ℝ) : ℂ) = 0 := by
    push_cast
    linear_combination -hgm
  have hreal : b m₀ / m₀ * δ = 0 := by exact_mod_cast hC
  rcases mul_eq_zero.mp hreal with h | h
  · rcases div_eq_zero_iff.mp h with h | h
    · exact h
    · exact absurd h hm₀pos.ne'
  · exact absurd h hδ0.ne'

/-- **Rigidity of dilated von Mangoldt weights.**  If `Λ(n) + Σ_{m ∈ S} b(m) Λ(n/m)` is
Weil-positive, then `b` vanishes on `S`. -/
theorem dilatedVonMangoldt_eq_zero_of_weilPositive {S : Finset ℕ} (hS : ∀ m ∈ S, 1 ≤ m)
    (b : ℕ → ℝ) (hW : WeilPositive fun n => (Λ n : ℝ) + dilatedVonMangoldt S b n) :
    ∀ m ∈ S, b m = 0 := by
  have hbig : ∀ m ∈ S, 2 ≤ m → b m = 0 := fun m hm h2 =>
    dilation_coeff_eq_zero_of_weilPositive hS b hW hm h2
  intro m hm
  by_cases h2 : 2 ≤ m
  · exact hbig m hm h2
  have hm1 : m = 1 := by have := hS m hm; omega
  subst hm1
  by_contra hb
  have hlam : (fun n => (Λ n : ℝ) + dilatedVonMangoldt S b n) =
      fun n => (1 + b 1) * ArithmeticFunction.vonMangoldt n := by
    funext n
    have hd : dilatedVonMangoldt S b n = b 1 * Λ n := by
      unfold dilatedVonMangoldt
      rw [Finset.sum_eq_single 1]
      · simp
      · intro k hk hk1
        have hk2 : 2 ≤ k := by have := hS k hk; omega
        simp [hbig k hk hk2]
      · intro h; exact absurd hm h
    rw [hd]; ring
  rw [hlam] at hW
  obtain ⟨a, ha, f, hf, hsupp, h1, h2', hneg⟩ :=
    scaled_vonMangoldt_weilAtomSymbol_not_nonneg (c := 1 + b 1) (by intro h; apply hb; linarith)
  exact absurd (hW a ha f hf hsupp h1 h2') (not_le.mpr hneg)

end RHTower
