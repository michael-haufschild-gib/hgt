import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheMellinTransformOfAStencil
import GaloisForLFunctions.RHTower.ZetaLogDerivResidue
import GaloisForLFunctions.RigidArithmeticOfCuts.TheCutIdentity
import GaloisForLFunctions.RigidArithmeticOfCuts.TheLiouvilleChebyshevIdentity

/-!
# A parity bound confines the zeros

The parity ledger `P_c(x) = Σ_k c(k) λ(k) L(⌊x/k⌋)` is the term that pays the factor `2` of sieve parity. Its generating
function is `D_{cλ}(s) ζ(2s)/ζ(s)`, with `D_{cλ}(s) = Σ c(k) λ(k) k^{-s}` the twisted Dirichlet polynomial. Unlike a
linear ledger of `Λ`, it is **not blind**: it has a pole at each zero of `ζ` that the twist does not annihilate.

So a bound `|P_c(x)| ≤ C x^a` confines the zeros: **every zero with `Re ρ > max(a, ½)` is a zero of `D_{cλ}`**.

The Mertens level bounds the ledger (`abs_parityLedger_le`), and the converse is exactly this confinement. A stencil
whose twist is free of zeros reads the zero-free region itself: for `c = δ₁` a bound on `L` gives a zero-free strip.
A parity bound can be weaker than a Mertens bound only by letting `D_{cλ}` absorb the zeros, and a Dirichlet
polynomial can do this for a finite set, which is the one-off world.
-/

open Finset Filter Topology Complex
open ArithmeticFunction (moebius)
open scoped LSeries.notation
open GaloisForLFunctions.ArithmeticKreinLangerTheory
open GaloisForLFunctions.ArithmeticAuxiliaryDynamics

noncomputable section

namespace GaloisForLFunctions.RigidArithmeticOfCuts

/-- The twisted Dirichlet polynomial `D_{cλ}(s) = Σ c(k) λ(k) k^{-s}`. -/
def twistPoly (c : ℕ →₀ ℤ) (s : ℂ) : ℂ :=
  ∑ k ∈ c.support, (c k : ℂ) * (ArithmeticFunction.liouville k : ℂ) * ((k : ℝ) : ℂ) ^ (-s)

/-- The partial sums of the Liouville Dirichlet series. -/
private def liouvilleHead (s : ℂ) (M : ℕ) : ℂ :=
  ∑ i ∈ Ioc 0 M, (ArithmeticFunction.liouville i : ℂ) * ((i : ℝ) : ℂ) ^ (-s)

private lemma liouvilleR_succ (M : ℕ) :
    liouvilleR (M + 1) = liouvilleR M + (ArithmeticFunction.liouville (M + 1) : ℝ) := by
  rw [liouvilleR, liouvilleR, sum_Ioc_succ_top (Nat.zero_le M)]

/-- **Exact Abel summation for a dilated Liouville sum.** -/
private lemma sum_liouvilleR_mul_abelStep (k : ℕ) (s : ℂ) (N : ℕ) :
    ∑ j ∈ range N, (liouvilleR ((j + 1) / k) : ℂ) * abelStep s j =
      ((k : ℝ) : ℂ) ^ (-s) * liouvilleHead s (N / k) -
        (liouvilleR (N / k) : ℂ) * (((N : ℝ) + 1 : ℝ) : ℂ) ^ (-s) := by
  induction N with
  | zero => simp [liouvilleHead, liouvilleR]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, abelStep]
    have hcast : (((N + 1 : ℕ) : ℝ) + 1 : ℝ) = (N : ℝ) + 2 := by push_cast; ring
    rw [hcast]
    by_cases hd : k ∣ N + 1
    · have hq : (N + 1) / k = N / k + 1 := by rw [Nat.succ_div, if_pos hd]
      have hmul : k * (N / k + 1) = N + 1 := by rw [← hq]; exact Nat.mul_div_cancel' hd
      have hval : ((k : ℝ) : ℂ) ^ (-s) * (((N / k + 1 : ℕ) : ℝ) : ℂ) ^ (-s) =
          (((N : ℝ) + 1 : ℝ) : ℂ) ^ (-s) := by
        have h1 : ((N : ℝ) + 1 : ℝ) = (k : ℝ) * ((N / k + 1 : ℕ) : ℝ) := by
          exact_mod_cast hmul.symm
        rw [h1, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg k) (Nat.cast_nonneg _)]
      rw [hq, liouvilleHead, liouvilleHead, sum_Ioc_succ_top (Nat.zero_le _), liouvilleR_succ, mul_add]
      have hstep : ((k : ℝ) : ℂ) ^ (-s) * ((ArithmeticFunction.liouville (N / k + 1) : ℂ) *
          (((N / k + 1 : ℕ) : ℝ) : ℂ) ^ (-s)) =
          (ArithmeticFunction.liouville (N / k + 1) : ℂ) * (((N : ℝ) + 1 : ℝ) : ℂ) ^ (-s) := by
        rw [← hval]
        ring
      rw [hstep]
      push_cast
      ring
    · have hq : (N + 1) / k = N / k := by rw [Nat.succ_div, if_neg hd, add_zero]
      rw [hq]
      ring

/-- The Dirichlet series of `λ` on `Re s > 1`. -/
private lemma tendsto_liouvilleHead {s : ℂ} (hs : 1 < s.re) :
    Tendsto (liouvilleHead s) atTop (𝓝 (LSeries (↗RHTower.liouvilleC) s)) := by
  have hsm := RHTower.LSeriesSummable_liouvilleC hs
  have h := hsm.hasSum.tendsto_sum_nat
  have h2 := h.comp (tendsto_add_atTop_nat 1)
  refine h2.congr fun M => ?_
  simp only [Function.comp, liouvilleHead]
  have hIoc : ∑ i ∈ Ioc 0 M, (ArithmeticFunction.liouville i : ℂ) * ((i : ℝ) : ℂ) ^ (-s) =
      ∑ i ∈ range M, (ArithmeticFunction.liouville (i + 1) : ℂ) * (((i + 1 : ℕ) : ℝ) : ℂ) ^ (-s) := by
    have : Ioc 0 M = Icc 1 M := by
      ext x
      simp only [mem_Ioc, mem_Icc]
      omega
    rw [this, sum_Icc_one_eq_sum_range]
  rw [hIoc, Finset.sum_range_succ']
  simp only [LSeries.term_zero, add_zero]
  refine sum_congr rfl fun i _ => ?_
  rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero i), RHTower.liouvilleC_apply, Complex.cpow_neg,
    div_eq_mul_inv]
  push_cast
  rfl

private lemma abs_liouvilleR_le_self (N : ℕ) : |liouvilleR N| ≤ N := by
  rw [liouvilleR]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc _ ≤ ∑ _j ∈ Ioc 0 N, (1 : ℝ) := sum_le_sum fun j hj => by
        rw [ArithmeticFunction.liouville_apply (Nat.pos_iff_ne_zero.mp (mem_Ioc.mp hj).1)]
        push_cast
        simp [abs_pow]
    _ = N := by simp

/-- The boundary term of the Abel sum vanishes on `Re s > 1`. -/
private lemma tendsto_boundary (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun N : ℕ => (liouvilleR (N / k) : ℂ) * (((N : ℝ) + 1 : ℝ) : ℂ) ^ (-s)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hexp : Tendsto (fun N : ℕ => ((N : ℝ) + 1) ^ (1 - s.re)) atTop (𝓝 0) := by
    have h1 := tendsto_rpow_neg_atTop (y := s.re - 1) (by linarith)
    have h2 : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    refine (h1.comp h2).congr fun N => ?_
    simp only [Function.comp, neg_sub]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_) hexp
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hN, Complex.neg_re, Complex.norm_real,
    Real.norm_eq_abs]
  have h1 : |liouvilleR (N / k)| ≤ (N : ℝ) + 1 := by
    refine (abs_liouvilleR_le_self _).trans ?_
    have : ((N / k : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.div_le_self N k
    linarith
  calc |liouvilleR (N / k)| * ((N : ℝ) + 1) ^ (-s.re)
      ≤ ((N : ℝ) + 1) * ((N : ℝ) + 1) ^ (-s.re) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = ((N : ℝ) + 1) ^ (1 - s.re) := by
        rw [sub_eq_add_neg, Real.rpow_add hN, Real.rpow_one]

/-- The parity ledger read by the Abel kernel, on `Re s > 1`. -/
private lemma tendsto_sum_parityLedger_mul_abelStep {c : ℕ →₀ ℤ} (hc0 : c 0 = 0) {s : ℂ}
    (hs : 1 < s.re) :
    Tendsto (fun N : ℕ => ∑ j ∈ range N, (parityLedger c (j + 1) : ℂ) * abelStep s j) atTop
      (𝓝 (twistPoly c s * LSeries (↗RHTower.liouvilleC) s)) := by
  have hexp : ∀ N : ℕ, ∑ j ∈ range N, (parityLedger c (j + 1) : ℂ) * abelStep s j =
      ∑ k ∈ c.support, (c k : ℂ) * (ArithmeticFunction.liouville k : ℂ) *
        ∑ j ∈ range N, (liouvilleR ((j + 1) / k) : ℂ) * abelStep s j := by
    intro N
    simp only [parityLedger, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun j _ => ?_
    push_cast
    rw [sum_mul]
    exact sum_congr rfl fun k _ => by ring
  simp only [hexp]
  rw [twistPoly, sum_mul]
  refine tendsto_finsetSum _ fun k hk => ?_
  have hk0 : 0 < k := Nat.pos_of_ne_zero fun h => by
    subst h
    exact Finsupp.mem_support_iff.mp hk hc0
  have hval : (c k : ℂ) * (ArithmeticFunction.liouville k : ℂ) * ((k : ℝ) : ℂ) ^ (-s) *
      LSeries (↗RHTower.liouvilleC) s =
      (c k : ℂ) * (ArithmeticFunction.liouville k : ℂ) *
        (((k : ℝ) : ℂ) ^ (-s) * LSeries (↗RHTower.liouvilleC) s - 0) := by
    ring
  rw [hval]
  refine Tendsto.const_mul _ ?_
  simp only [sum_liouvilleR_mul_abelStep k]
  refine Tendsto.sub (Tendsto.const_mul _ ?_) (tendsto_boundary k hs)
  have hN : Tendsto (fun N : ℕ => N / k) atTop atTop := Nat.tendsto_div_const_atTop hk0.ne'
  exact (tendsto_liouvilleHead hs).comp hN

/-- **A parity bound confines the zeros.** If `|P_c(x)| ≤ C x^a`, then every zero of `ζ` with `Re ρ > max(a, ½)`
is a zero of the twisted polynomial `D_{cλ}`. -/
theorem twistPoly_eq_zero_of_parity_bound {c : ℕ →₀ ℤ} (hc0 : c 0 = 0) {C a : ℝ} (hC : 0 ≤ C)
    (hP : ∀ x : ℕ, 1 ≤ x → |parityLedger c x| ≤ C * (x : ℝ) ^ a) {ρ : ℂ} (hζ : riemannZeta ρ = 0)
    (hρ1 : ρ ≠ 1) (ha : a < ρ.re) (hh : 1 / 2 < ρ.re) : twistPoly c ρ = 0 := by
  classical
  set b : ℝ := max a (1 / 2) with hb
  have hba : a ≤ b := le_max_left _ _
  have hbh : 1 / 2 ≤ b := le_max_right _ _
  set U : Set ℂ := {s | b < s.re} with hU
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUconn : IsPreconnected U := (convex_halfSpace_re_gt b).isPreconnected
  set F : ℂ → ℂ := fun s => ∑' j : ℕ, (parityLedger c (j + 1) : ℂ) * abelStep s j with hF
  -- The bound on the terms.
  have hterm : ∀ (j : ℕ) {s : ℂ}, 0 < s.re → ‖(parityLedger c (j + 1) : ℂ) * abelStep s j‖ ≤
      C * ‖s‖ * ((j : ℝ) + 1) ^ (a - s.re - 1) := by
    intro j s hs
    have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h1 := hP (j + 1) (by omega)
    have h2 := norm_abelStep_le_rpow hs j
    push_cast at h1
    calc _ ≤ (C * ((j : ℝ) + 1) ^ a) * (‖s‖ * ((j : ℝ) + 1) ^ (-s.re - 1)) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = C * ‖s‖ * (((j : ℝ) + 1) ^ a * ((j : ℝ) + 1) ^ (-s.re - 1)) := by ring
      _ = _ := by
          rw [← Real.rpow_add hj]
          congr 2
          ring
  have hsummable : ∀ {s : ℂ}, b < s.re →
      Summable fun j : ℕ => (parityLedger c (j + 1) : ℂ) * abelStep s j := by
    intro s hs
    have hs0 : 0 < s.re := by linarith
    refine Summable.of_norm_bounded ?_ fun j => hterm j hs0
    refine Summable.mul_left _ ?_
    have h := (summable_nat_add_iff 1).mpr
      (Real.summable_nat_rpow.mpr (by linarith : a - s.re - 1 < -1))
    refine h.congr fun j => ?_
    push_cast
    rfl
  -- `F` is holomorphic.
  have hFan : AnalyticOnNhd ℂ F U := by
    intro z hz
    have hz' : b < z.re := hz
    set e0 : ℝ := (z.re - b) / 2 with he0
    have he0pos : 0 < e0 := by rw [he0]; linarith
    set R : ℝ := ‖z‖ + 1 with hR
    set V : Set ℂ := {s | b + e0 < s.re} ∩ Metric.ball 0 R with hV
    have hVopen : IsOpen V :=
      (isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball
    have hzV : z ∈ V := by
      refine ⟨?_, by simp [hR]⟩
      show b + e0 < z.re
      rw [he0]
      linarith
    have hdiff : DifferentiableOn ℂ F V := by
      have hsum : Summable fun j : ℕ => C * R * ((j : ℝ) + 1) ^ (-e0 - 1) := by
        refine Summable.mul_left _ ?_
        have h := (summable_nat_add_iff 1).mpr
          (Real.summable_nat_rpow.mpr (by linarith : -e0 - 1 < -1))
        refine h.congr fun j => ?_
        push_cast
        rfl
      refine differentiableOn_tsum_of_summable_norm hsum (fun j => ?_) hVopen (fun j s hs => ?_)
      · refine DifferentiableOn.const_mul ?_ _
        refine Differentiable.differentiableOn ?_
        have hne : ∀ x : ℝ, 0 < x → ((x : ℝ) : ℂ) ≠ 0 := fun x hx => by exact_mod_cast hx.ne'
        unfold abelStep
        exact (differentiable_neg.const_cpow (Or.inl (hne _ (by positivity)))).sub
          (differentiable_neg.const_cpow (Or.inl (hne _ (by positivity))))
      · obtain ⟨hs1, hs2⟩ := hs
        have hs1' : b + e0 < s.re := hs1
        have hs0 : 0 < s.re := by linarith
        have hsR : ‖s‖ ≤ R := by simpa using (Metric.mem_ball.mp hs2).le
        refine (hterm j hs0).trans ?_
        have hj : (1 : ℝ) ≤ (j : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) j]
        have hexp : ((j : ℝ) + 1) ^ (a - s.re - 1) ≤ ((j : ℝ) + 1) ^ (-e0 - 1) :=
          Real.rpow_le_rpow_of_exponent_le hj (by linarith)
        have h1 : C * ‖s‖ ≤ C * R := mul_le_mul_of_nonneg_left hsR hC
        exact mul_le_mul h1 hexp (by positivity) (by positivity)
    exact (hdiff.analyticAt (hVopen.mem_nhds hzV))
  -- The two sides of the identity.
  set Z := _root_.RHTower.zetaResidueUnit with hZ
  have hZan : AnalyticOnNhd ℂ Z U := fun z _ => _root_.RHTower.analyticAt_zetaResidueUnit z
  have hG₁ : AnalyticOnNhd ℂ (fun s => F s * Z s) U := hFan.mul hZan
  have htwist : AnalyticOnNhd ℂ (twistPoly c) U := by
    intro z _
    refine Differentiable.analyticAt ?_ z
    unfold twistPoly
    refine Differentiable.fun_sum fun k hk => ?_
    have hk0 : 0 < k := Nat.pos_of_ne_zero fun h => by
      subst h
      exact Finsupp.mem_support_iff.mp hk hc0
    have hne : ((k : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hk0.ne'
    exact (differentiable_neg.const_cpow (Or.inl hne)).const_mul _
  have hζ2 : AnalyticOnNhd ℂ (fun s => riemannZeta (2 * s)) U := by
    have hopen : IsOpen U := hUopen
    have hd : DifferentiableOn ℂ (fun s => riemannZeta (2 * s)) U := by
      intro z hz
      have hz' : b < z.re := hz
      have hne : 2 * z ≠ 1 := by
        intro h
        have := congrArg Complex.re h
        simp at this
        linarith
      exact ((differentiableAt_riemannZeta hne).comp z (by fun_prop)).differentiableWithinAt
    exact hd.analyticOnNhd hopen
  have hsub1 : AnalyticOnNhd ℂ (fun s : ℂ => s - 1) U := fun _ _ =>
    analyticAt_id.sub analyticAt_const
  have hG₂ : AnalyticOnNhd ℂ (fun s => twistPoly c s * ((s - 1) * riemannZeta (2 * s))) U :=
    htwist.mul (hsub1.mul hζ2)
  -- Equality far to the right.
  set σ₀ : ℝ := max a 1 + 1 with hσ₀
  have hσa : a < σ₀ := by
    have := le_max_left a 1
    rw [hσ₀]
    linarith
  have hσ1 : 1 < σ₀ := by
    have := le_max_right a 1
    rw [hσ₀]
    linarith
  have hσb : b < σ₀ := by
    rw [hb]
    exact max_lt hσa (by linarith)
  have hmem : ((σ₀ : ℝ) : ℂ) ∈ U := by simpa [hU] using hσb
  have heq : (fun s => F s * Z s) =ᶠ[𝓝 ((σ₀ : ℝ) : ℂ)]
      fun s => twistPoly c s * ((s - 1) * riemannZeta (2 * s)) := by
    have hnhds : {s : ℂ | max b 1 < s.re} ∈ 𝓝 ((σ₀ : ℝ) : ℂ) := by
      refine (isOpen_lt continuous_const Complex.continuous_re).mem_nhds ?_
      simpa using max_lt hσb hσ1
    filter_upwards [hnhds] with s hs
    have hs' : max b 1 < s.re := hs
    have hsb : b < s.re := (le_max_left _ _).trans_lt hs'
    have hs1 : 1 < s.re := (le_max_right _ _).trans_lt hs'
    have hne1 : s ≠ 1 := fun h => by
      rw [h] at hs1
      simp at hs1
    have hval : F s = twistPoly c s * LSeries (↗RHTower.liouvilleC) s :=
      tendsto_nhds_unique (hsummable hsb).hasSum.tendsto_sum_nat
        (tendsto_sum_parityLedger_mul_abelStep hc0 hs1)
    have hZs : Z s = (s - 1) * riemannZeta s :=
      (_root_.RHTower.zetaResidueUnit_eventuallyEq hne1).eq_of_nhds
    have hL := RHTower.LSeries_liouvilleC_mul_riemannZeta hs1
    simp only [hval, hZs, ← hL]
    ring
  have hall := hG₁.eqOn_of_preconnected_of_eventuallyEq hG₂ hUconn hmem heq
  have hρU : ρ ∈ U := by
    show b < ρ.re
    rw [hb]
    exact max_lt ha hh
  have hat := hall hρU
  simp only at hat
  have hZρ : Z ρ = (ρ - 1) * riemannZeta ρ :=
    (_root_.RHTower.zetaResidueUnit_eventuallyEq hρ1).eq_of_nhds
  rw [hZρ, hζ, mul_zero, mul_zero] at hat
  have hne2 : riemannZeta (2 * ρ) ≠ 0 := by
    refine riemannZeta_ne_zero_of_one_le_re ?_
    simp
    linarith
  have hsub : ρ - 1 ≠ 0 := sub_ne_zero.mpr hρ1
  have := (mul_eq_zero.mp hat.symm).resolve_right (mul_ne_zero hsub hne2)
  exact this

private lemma liouville_one : ArithmeticFunction.liouville 1 = 1 := by
  rw [ArithmeticFunction.liouville_apply one_ne_zero]
  simp

/-- The twist of the trivial stencil is `1`. -/
theorem twistPoly_single_one (s : ℂ) : twistPoly (Finsupp.single 1 1) s = 1 := by
  rw [twistPoly, Finsupp.support_single _ one_ne_zero, sum_singleton, liouville_one]
  simp

/-- The parity ledger of the trivial stencil is `L`. -/
theorem parityLedger_single_one (x : ℕ) : parityLedger (Finsupp.single 1 1) x = liouvilleR x := by
  rw [parityLedger, Finsupp.support_single _ one_ne_zero, sum_singleton, liouville_one]
  simp

/-- **A bound on `L` is a zero-free strip.** -/
theorem riemannZeta_ne_zero_of_liouville_bound {C a : ℝ} (hC : 0 ≤ C)
    (hL : ∀ x : ℕ, 1 ≤ x → |liouvilleR x| ≤ C * (x : ℝ) ^ a) {ρ : ℂ} (hρ1 : ρ ≠ 1) (ha : a < ρ.re)
    (hh : 1 / 2 < ρ.re) : riemannZeta ρ ≠ 0 := by
  intro hζ
  have h := twistPoly_eq_zero_of_parity_bound (c := Finsupp.single 1 1) (by simp) hC
    (fun x hx => by rw [parityLedger_single_one]; exact hL x hx) hζ hρ1 ha hh
  rw [twistPoly_single_one] at h
  exact one_ne_zero h

end GaloisForLFunctions.RigidArithmeticOfCuts
