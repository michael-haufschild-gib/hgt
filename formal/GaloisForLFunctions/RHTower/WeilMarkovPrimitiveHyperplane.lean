import GaloisForLFunctions.RHTower.WeilMarkovOddPositivity
import GaloisForLFunctions.RHTower.LebesgueAtomWeilPositivity

/-!
# RH is positivity of the archimedean-minus-prime form on the primitive hyperplane

Let `M(f) = Re[(1/2π) ∫ k̂ γ − Σ_{n ≥ 2} Λ(n) n^{−1/2}(k(log n) + k(−log n))]`, `k = f ⋆ f̃`
(`markovEnergy`). For a real test `F` let `C(F) = ∫ F(x) cosh(x/2) dx`.

**Theorem** (`riemannHypothesis_iff_forall_cosh_moment_zero_markovEnergy_nonneg`). RH holds if and
only if `M(F) ≥ 0` for every real `C²` compactly supported `F` with `C(F) = 0`.

The truncated Riemann kernel has `M < 0` (`exists_markovEnergy_neg`), so this is the
one-negative-square law in the form of the Hodge index theorem. The hyperplane `C = 0` is the
`M`-orthogonal complement of Riemann's kernel `Φ`, which plays the ample class, and `M` is
nonnegative on this primitive hyperplane.

Proof.
* **Parity split** (`markovEnergy_ofReal_eq_even_add_odd`). For real `F = F_e + F_o`, the transform
  `F̂_e` is real and `F̂_o` purely imaginary on `ℝ`, so `|F̂|² = |F̂_e|² + |F̂_o|²`. The cross
  autocorrelations `F_e ⋆ F_o` and `F_o ⋆ F_e` are odd, so they vanish at `±log n` in sum. Hence
  `M(F) = M(F_e) + M(F_o)`.
* Under RH, `M(F_o) ≥ 0` (`odd_markovEnergy_nonneg_of_riemannHypothesis`). Moreover
  `C(F_e) = C(F) = 0` makes `F_e` pole-free, so `M(F_e) = W(F_e) ≥ 0`.
* Conversely, every odd test has `C = 0`, and positivity on odd tests is RH
  (`riemannHypothesis_iff_forall_odd_markovEnergy_nonneg`).
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate
open Zeta23

namespace RHTower

noncomputable section

/-! ## Even and odd parts -/

/-- The even part `(F(x) + F(−x))/2`. -/
def evenPartReal (F : ℝ → ℝ) (x : ℝ) : ℝ := (F x + F (-x)) / 2

/-- The odd part `(F(x) − F(−x))/2`. -/
def oddPartReal (F : ℝ → ℝ) (x : ℝ) : ℝ := (F x - F (-x)) / 2

theorem evenPartReal_add_oddPartReal (F : ℝ → ℝ) (x : ℝ) :
    evenPartReal F x + oddPartReal F x = F x := by
  unfold evenPartReal oddPartReal; ring

theorem evenPartReal_neg (F : ℝ → ℝ) (x : ℝ) : evenPartReal F (-x) = evenPartReal F x := by
  unfold evenPartReal; rw [neg_neg]; ring

theorem oddPartReal_neg (F : ℝ → ℝ) (x : ℝ) : oddPartReal F (-x) = -oddPartReal F x := by
  unfold oddPartReal; rw [neg_neg]; ring

theorem contDiff_evenPartReal {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) : ContDiff ℝ 2 (evenPartReal F) :=
  (hF.add (hF.comp contDiff_neg)).div_const 2

theorem contDiff_oddPartReal {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) : ContDiff ℝ 2 (oddPartReal F) :=
  (hF.sub (hF.comp contDiff_neg)).div_const 2

theorem hasCompactSupport_evenPartReal {F : ℝ → ℝ} (hF : HasCompactSupport F) :
    HasCompactSupport (evenPartReal F) := by
  have h2 : HasCompactSupport (fun x => F (-x)) := hF.comp_homeomorph (Homeomorph.neg ℝ)
  have h3 := (hF.add h2).comp_left (g := fun y : ℝ => y / 2) (by norm_num)
  convert h3 using 1
  funext x
  simp [evenPartReal, Function.comp]

theorem hasCompactSupport_oddPartReal {F : ℝ → ℝ} (hF : HasCompactSupport F) :
    HasCompactSupport (oddPartReal F) := by
  have h2 : HasCompactSupport (fun x => F (-x)) := hF.comp_homeomorph (Homeomorph.neg ℝ)
  have h3 := (hF.sub h2).comp_left (g := fun y : ℝ => y / 2) (by norm_num)
  convert h3 using 1
  funext x
  simp [oddPartReal, Function.comp]

/-! ## The transform splits orthogonally -/

theorem paperFT_ofReal_conj_of_even {u : ℝ → ℝ} (heven : ∀ x, u (-x) = u x) (r : ℝ) :
    (starRingEnd ℂ) (paperFT (fun x => (u x : ℂ)) r) = paperFT (fun x => (u x : ℂ)) r := by
  rw [conj_paperFT_ofReal, Complex.conj_ofReal, paperFT_ofReal_neg_of_even heven]

theorem paperFT_ofReal_conj_of_odd {u : ℝ → ℝ} (hodd : ∀ x, u (-x) = -u x) (r : ℝ) :
    (starRingEnd ℂ) (paperFT (fun x => (u x : ℂ)) r) = -paperFT (fun x => (u x : ℂ)) r := by
  rw [conj_paperFT_ofReal, Complex.conj_ofReal, paperFT_ofReal_neg_of_odd hodd]

/-- A self-conjugate and an anti-self-conjugate number are orthogonal. -/
theorem normSq_add_of_conj_eq_of_conj_eq_neg {a b : ℂ} (ha : (starRingEnd ℂ) a = a)
    (hb : (starRingEnd ℂ) b = -b) : Complex.normSq (a + b) = Complex.normSq a + Complex.normSq b := by
  rw [Complex.normSq_add]
  have hre : (a * (starRingEnd ℂ) b).re = 0 := by
    rw [hb]
    have hc : (starRingEnd ℂ) (a * b) = -(a * b) := by rw [map_mul, ha, hb]; ring
    have h1 := congrArg Complex.re hc
    rw [Complex.conj_re, Complex.neg_re] at h1
    rw [mul_neg, Complex.neg_re]
    linarith
  rw [hre]
  ring

theorem norm_sq_paperFT_ofReal_eq_even_add_odd {F : ℝ → ℝ} (hF : Continuous F)
    (hFc : HasCompactSupport F) (r : ℝ) :
    ‖paperFT (fun x => (F x : ℂ)) r‖ ^ 2 =
      ‖paperFT (fun x => (evenPartReal F x : ℂ)) r‖ ^ 2 +
        ‖paperFT (fun x => (oddPartReal F x : ℂ)) r‖ ^ 2 := by
  have hFe : Continuous (evenPartReal F) := (hF.add (hF.comp continuous_neg)).div_const 2
  have hFo : Continuous (oddPartReal F) := (hF.sub (hF.comp continuous_neg)).div_const 2
  have hsplit : paperFT (fun x => (F x : ℂ)) r =
      paperFT (fun x => (evenPartReal F x : ℂ)) r + paperFT (fun x => (oddPartReal F x : ℂ)) r := by
    have e : (fun x => (F x : ℂ)) = fun x => (1 : ℂ) * (evenPartReal F x : ℂ) +
        (1 : ℂ) * (oddPartReal F x : ℂ) := by
      funext x
      rw [one_mul, one_mul, ← Complex.ofReal_add, evenPartReal_add_oddPartReal]
    rw [e, paperFT_smul_add_smul (F := fun x => ((evenPartReal F x : ℝ) : ℂ))
      (G := fun x => ((oddPartReal F x : ℝ) : ℂ)) 1 1 _
      (integrable_mul_cexp_of_compact (Complex.continuous_ofReal.comp hFe)
        ((hasCompactSupport_evenPartReal hFc).comp_left Complex.ofReal_zero) _)
      (integrable_mul_cexp_of_compact (Complex.continuous_ofReal.comp hFo)
        ((hasCompactSupport_oddPartReal hFc).comp_left Complex.ofReal_zero) _), one_mul, one_mul]
  rw [hsplit, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  exact normSq_add_of_conj_eq_of_conj_eq_neg
    (paperFT_ofReal_conj_of_even (evenPartReal_neg F) r)
    (paperFT_ofReal_conj_of_odd (oddPartReal_neg F) r)

/-! ## The autocorrelation splits up to odd cross terms -/

theorem crossCorr_even_odd_neg {E O : ℝ → ℝ} (heven : ∀ x, E (-x) = E x)
    (hodd : ∀ x, O (-x) = -O x) (y : ℝ) : crossCorr E O (-y) = -crossCorr E O y := by
  unfold crossCorr
  rw [← integral_neg, ← integral_neg_eq_self]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only
  rw [heven, show -t - -y = -(t - y) by ring, hodd]
  ring

theorem crossCorr_odd_even_neg {E O : ℝ → ℝ} (heven : ∀ x, E (-x) = E x)
    (hodd : ∀ x, O (-x) = -O x) (y : ℝ) : crossCorr O E (-y) = -crossCorr O E y := by
  unfold crossCorr
  rw [← integral_neg, ← integral_neg_eq_self]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only
  rw [hodd, show -t - -y = -(t - y) by ring, heven]
  ring

theorem crossCorr_add_add {E O : ℝ → ℝ} (hE : Continuous E) (hEc : HasCompactSupport E)
    (hO : Continuous O) (hOc : HasCompactSupport O) (y : ℝ) :
    crossCorr (fun x => E x + O x) (fun x => E x + O x) y =
      crossCorr E E y + crossCorr O O y + (crossCorr E O y + crossCorr O E y) := by
  unfold crossCorr
  have i1 := integrable_translate_prod hE hEc hE y
  have i2 := integrable_translate_prod hE hEc hO y
  have i3 := integrable_translate_prod hO hOc hE y
  have i4 := integrable_translate_prod hO hOc hO y
  have e : (fun t => (E t + O t) * (E (t - y) + O (t - y))) =
      fun t => (E t * E (t - y) + O t * O (t - y)) + (E t * O (t - y) + O t * E (t - y)) := by
    funext t; ring
  have j1 : Integrable fun t => E t * E (t - y) + O t * O (t - y) := i1.add i4
  have j2 : Integrable fun t => E t * O (t - y) + O t * E (t - y) := i2.add i3
  rw [e, integral_add j1 j2, integral_add i1 i4, integral_add i2 i3]

/-! ## The parity split of the archimedean-minus-prime energy -/

/-- The prime coefficients `Λ(n)/√n` on `n ≥ 2`. -/
def vonMangoldtAtom (n : ℕ) : ℝ :=
  if 2 ≤ n then (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n else 0

theorem markovEnergy_eq_arch_sub_primes_atom (f : ℝ → ℂ) :
    markovEnergy f = ((1 / (2 * π) : ℂ) * (∫ r : ℝ, paperFT (EF.weilTest f f) r *
        (EF.gammaBracket r : ℂ)) -
      ∑' n : ℕ, ((vonMangoldtAtom n : ℝ) : ℂ) *
        (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n))).re :=
  markovEnergy_eq_arch_sub_primes f

/-- **Parity split.** For real `F`, `M(F) = M(F_e) + M(F_o)`. -/
theorem markovEnergy_ofReal_eq_even_add_odd {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hFc : HasCompactSupport F) :
    markovEnergy (fun x => (F x : ℂ)) =
      markovEnergy (fun x => (evenPartReal F x : ℂ)) +
        markovEnergy (fun x => (oddPartReal F x : ℂ)) := by
  set Fe := evenPartReal F
  set Fo := oddPartReal F
  have hFed := contDiff_evenPartReal hF
  have hFod := contDiff_oddPartReal hF
  have hFec := hasCompactSupport_evenPartReal hFc
  have hFoc := hasCompactSupport_oddPartReal hFc
  set U : ℝ → ℂ := fun x => (F x : ℂ)
  set Ue : ℝ → ℂ := fun x => (Fe x : ℂ)
  set Uo : ℝ → ℂ := fun x => (Fo x : ℂ)
  have hUd : ContDiff ℝ 2 U := Complex.ofRealCLM.contDiff.comp hF
  have hUc : HasCompactSupport U := hFc.comp_left Complex.ofReal_zero
  have hUed : ContDiff ℝ 2 Ue := Complex.ofRealCLM.contDiff.comp hFed
  have hUec : HasCompactSupport Ue := hFec.comp_left Complex.ofReal_zero
  have hUod : ContDiff ℝ 2 Uo := Complex.ofRealCLM.contDiff.comp hFod
  have hUoc : HasCompactSupport Uo := hFoc.comp_left Complex.ofReal_zero
  -- archimedean part
  have harch : (∫ r : ℝ, paperFT (EF.weilTest U U) r * (EF.gammaBracket r : ℂ)) =
      (∫ r : ℝ, paperFT (EF.weilTest Ue Ue) r * (EF.gammaBracket r : ℂ)) +
        ∫ r : ℝ, paperFT (EF.weilTest Uo Uo) r * (EF.gammaBracket r : ℂ) := by
    rw [← integral_add (LebesgueAtomWeil.integrable_paperFT_weilTest_mul_gammaBracket hUed hUec hUed hUec)
      (LebesgueAtomWeil.integrable_paperFT_weilTest_mul_gammaBracket hUod hUoc hUod hUoc)]
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    simp only
    rw [paperFT_weilTest_self_ofReal hUd.continuous hUc,
      paperFT_weilTest_self_ofReal hUed.continuous hUec,
      paperFT_weilTest_self_ofReal hUod.continuous hUoc,
      norm_sq_paperFT_ofReal_eq_even_add_odd hF.continuous hFc r]
    push_cast; ring
  -- prime part
  have hk : ∀ y : ℝ, EF.weilTest U U y = EF.weilTest Ue Ue y + EF.weilTest Uo Uo y +
      ((crossCorr Fe Fo y + crossCorr Fo Fe y : ℝ) : ℂ) := by
    intro y
    have hFsum : (fun x => Fe x + Fo x) = F := funext (evenPartReal_add_oddPartReal F)
    have := crossCorr_add_add hFed.continuous hFec hFod.continuous hFoc y
    rw [hFsum] at this
    rw [weilTest_ofReal_eq, weilTest_ofReal_eq, weilTest_ofReal_eq]
    change ((crossCorr F F y : ℝ) : ℂ) = ((crossCorr Fe Fe y : ℝ) : ℂ) +
      ((crossCorr Fo Fo y : ℝ) : ℂ) + ((crossCorr Fe Fo y + crossCorr Fo Fe y : ℝ) : ℂ)
    rw [this]
    push_cast; ring
  have hcross : ∀ y : ℝ, crossCorr Fe Fo y + crossCorr Fo Fe y +
      (crossCorr Fe Fo (-y) + crossCorr Fo Fe (-y)) = 0 := by
    intro y
    rw [crossCorr_even_odd_neg (evenPartReal_neg F) (oddPartReal_neg F),
      crossCorr_odd_even_neg (evenPartReal_neg F) (oddPartReal_neg F)]
    ring
  have hprime : (∑' n : ℕ, ((vonMangoldtAtom n : ℝ) : ℂ) *
        (EF.weilTest U U (Real.log n) + EF.weilTest U U (-Real.log n))) =
      (∑' n : ℕ, ((vonMangoldtAtom n : ℝ) : ℂ) *
        (EF.weilTest Ue Ue (Real.log n) + EF.weilTest Ue Ue (-Real.log n))) +
      ∑' n : ℕ, ((vonMangoldtAtom n : ℝ) : ℂ) *
        (EF.weilTest Uo Uo (Real.log n) + EF.weilTest Uo Uo (-Real.log n)) := by
    rw [← (summable_primeAtoms vonMangoldtAtom (EF.weilTest_hasCompactSupport hUec hUec)).tsum_add
      (summable_primeAtoms vonMangoldtAtom (EF.weilTest_hasCompactSupport hUoc hUoc))]
    refine tsum_congr fun n => ?_
    rw [hk, hk]
    have hz := hcross (Real.log n)
    have : (((crossCorr Fe Fo (Real.log n) + crossCorr Fo Fe (Real.log n) : ℝ) : ℂ) +
        ((crossCorr Fe Fo (-Real.log n) + crossCorr Fo Fe (-Real.log n) : ℝ) : ℂ)) = 0 := by
      rw [← Complex.ofReal_add, hz, Complex.ofReal_zero]
    linear_combination ((vonMangoldtAtom n : ℝ) : ℂ) * this
  rw [markovEnergy_eq_arch_sub_primes_atom, markovEnergy_eq_arch_sub_primes_atom,
    markovEnergy_eq_arch_sub_primes_atom, harch, hprime]
  simp only [Complex.sub_re, Complex.add_re, mul_add]
  ring

/-! ## The primitive hyperplane -/

theorem integral_mul_cosh_half_of_odd {u : ℝ → ℝ} (hodd : ∀ x, u (-x) = -u x) :
    ∫ x, u x * Real.cosh (x / 2) = 0 := by
  have h : ∫ x, u x * Real.cosh (x / 2) = -∫ x, u x * Real.cosh (x / 2) := by
    rw [← integral_neg, ← integral_neg_eq_self]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [hodd, show -x / 2 = -(x / 2) by ring, Real.cosh_neg]
    ring
  linarith

theorem integral_mul_cosh_half_eq_exp_of_even {u : ℝ → ℝ} (heven : ∀ x, u (-x) = u x)
    (hu : Continuous u) (huc : HasCompactSupport u) :
    ∫ x, u x * Real.cosh (x / 2) = ∫ x, u x * Real.exp (-(x / 2)) := by
  have i1 : Integrable fun x => u x * Real.exp (x / 2) :=
    (hu.mul (by fun_prop)).integrable_of_hasCompactSupport huc.mul_right
  have i2 : Integrable fun x => u x * Real.exp (-(x / 2)) :=
    (hu.mul (by fun_prop)).integrable_of_hasCompactSupport huc.mul_right
  have e : (fun x => u x * Real.cosh (x / 2)) =
      fun x => (1 / 2 : ℝ) * (u x * Real.exp (x / 2) + u x * Real.exp (-(x / 2))) := by
    funext x; rw [Real.cosh_eq]; ring
  rw [e, integral_const_mul, integral_add i1 i2, integral_mul_exp_half_of_even heven]
  ring

/-- **RH is the one-negative-square law, Hodge-index form.** `M ≥ 0` on every real test with
vanishing cosh moment, the `M`-orthogonal complement of Riemann's kernel. -/
theorem riemannHypothesis_iff_forall_cosh_moment_zero_markovEnergy_nonneg :
    RiemannHypothesis ↔ ∀ F : ℝ → ℝ, ContDiff ℝ 2 F → HasCompactSupport F →
      ∫ x, F x * Real.cosh (x / 2) = 0 → 0 ≤ markovEnergy (fun x => (F x : ℂ)) := by
  constructor
  · intro hRH F hF hFc hC
    rw [markovEnergy_ofReal_eq_even_add_odd hF hFc]
    have hFed := contDiff_evenPartReal hF
    have hFec := hasCompactSupport_evenPartReal hFc
    have hodd := odd_markovEnergy_nonneg_of_riemannHypothesis hRH (contDiff_oddPartReal hF)
      (hasCompactSupport_oddPartReal hFc) (oddPartReal_neg F)
    -- the even part is pole-free
    have hCe : ∫ x, evenPartReal F x * Real.cosh (x / 2) = 0 := by
      have hFo := integral_mul_cosh_half_of_odd (oddPartReal_neg F)
      have i1 : Integrable fun x => evenPartReal F x * Real.cosh (x / 2) :=
        (hFed.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport hFec.mul_right
      have i2 : Integrable fun x => oddPartReal F x * Real.cosh (x / 2) :=
        ((contDiff_oddPartReal hF).continuous.mul (by fun_prop)).integrable_of_hasCompactSupport
          (hasCompactSupport_oddPartReal hFc).mul_right
      have hsum : ∫ x, F x * Real.cosh (x / 2) = (∫ x, evenPartReal F x * Real.cosh (x / 2)) +
          ∫ x, oddPartReal F x * Real.cosh (x / 2) := by
        rw [← integral_add i1 i2]
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only
        rw [← add_mul, evenPartReal_add_oddPartReal]
      linarith
    set Ue : ℝ → ℂ := fun x => (evenPartReal F x : ℂ)
    have hUed : ContDiff ℝ 2 Ue := Complex.ofRealCLM.contDiff.comp hFed
    have hUec : HasCompactSupport Ue := hFec.comp_left Complex.ofReal_zero
    have hp1 : paperFT Ue (I / 2) = 0 := by
      rw [paperFT_ofReal_I_half_eq_integral, ← integral_mul_cosh_half_eq_exp_of_even
        (evenPartReal_neg F) hFed.continuous hFec, hCe, Complex.ofReal_zero]
    have hp2 : paperFT Ue (-I / 2) = 0 := by
      rw [neg_div, paperFT_ofReal_neg_of_even (evenPartReal_neg F)]; exact hp1
    have hpole : weilPoleTerm (EF.weilTest Ue Ue) = 0 := by
      rw [weilPoleTerm_weilTest_eq hUed.continuous hUec, hp1, hp2]; simp
    have hW := (riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mp hRH) Ue hUed hUec
    have heven : 0 ≤ markovEnergy Ue := by
      rw [markovEnergy_eq_W_sub hUed hUec, hpole, Complex.zero_re, sub_zero,
        zeta_W_eq_weilFullFunctional hUed hUec]
      exact hW
    linarith
  · intro h
    refine riemannHypothesis_iff_forall_odd_markovEnergy_nonneg.mpr fun F hF hFc hodd => ?_
    exact h F hF hFc (integral_mul_cosh_half_of_odd hodd)

end

end RHTower
